// Santa 2026 - The Elf Calculator solver.
// Build:  g++ -O2 -std=c++17 -pthread -o solver src/solver.cpp
// Usage:  ./solver puzzles.csv out.csv [--threads N] [--nodes N] [--effort E] [--only ID]
//
// Per puzzle we keep a pool of register values and repeatedly produce the next
// target with the shortest construction we can find:
//   1. exact search up to depth 3 (4 with the S2 table) over the current pool
//   2. otherwise a best-first "reduction" search:  v = q*b +- c,  v = a +- x
//      that shrinks the value until the exact search can finish it.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
typedef __uint128_t u128;

static const int NREG_DEFAULT = 48;

struct HSet {
    vector<u64> t; int shift = 60; u64 mask = 0; size_t n = 0;
    void init(size_t cap) {
        size_t s = 16; int b = 4;
        while (s < cap * 2) { s <<= 1; b++; }
        if (t.size() != s) t.assign(s, 0); else memset(t.data(), 0, s * sizeof(u64));
        mask = s - 1; shift = 64 - b; n = 0;
    }
    inline u64 h(u64 x) const { return (x * 0x9E3779B97F4A7C15ULL) >> shift; }
    inline bool insert(u64 x) {
        u64 i = h(x);
        while (t[i]) { if (t[i] == x) return false; i = (i + 1) & mask; }
        t[i] = x; n++; return true;
    }
    inline bool has(u64 x) const {
        u64 i = h(x);
        while (t[i]) { if (t[i] == x) return true; i = (i + 1) & mask; }
        return false;
    }
};

struct Step { char op; u64 a, b, res; };
static inline u64 isqrt(u64 t) {
    u64 r = (u64)sqrtl((long double)t);
    while ((u128)r * r > t) r--;
    while ((u128)(r + 1) * (r + 1) <= t) r++;
    return r;
}
typedef vector<Step> Plan;

struct Params {
    int nodes = 200;       // expansions in the reduction search
    int effort = 1;        // 0: depth<=3 exact, 1: + S2 (depth 4), 2: + depth 5
    double rate = 5.5;     // bits per instruction assumed by the heuristic
    double minRate = 2.5;  // minimum bits gained per instruction for a move
    int small = 65536;      // values <= small are protected from eviction
    int keepBonus = 300;
    int vote = 1;
    double useW = 0, bitW = 0;
    int prime = 4;
    int primeMax = 6;
    int maxCand = 300;
};
static Params G;

struct Ctx {
    u64 L = 0;
    vector<u64> P;
    HSet Pset, S1, S2;
    vector<u64> S1list, S1sorted, S2list;
    bool s2built = false;

    inline int invs(u64 t, u64 c, u64* x, int* k) const {
        int n = 0;
        if (t > c) { x[n] = t - c; k[n++] = 0; }
        if (t + c <= L) { x[n] = t + c; k[n++] = 1; }
        if (c > t) { x[n] = c - t; k[n++] = 2; }
        if (c > 1 && t % c == 0) { x[n] = t / c; k[n++] = 3; }
        if (c > 1 && (u128)t * c <= L) { x[n] = t * c; k[n++] = 4; }
        if (t > 1 && c % t == 0 && c > t) { x[n] = c / t; k[n++] = 5; }
        return n;
    }
    static inline Step fin(int kind, u64 x, u64 c, u64 t) {
        switch (kind) {
            case 0: return {'+', x, c, t};
            case 1: return {'-', x, c, t};
            case 2: return {'-', c, x, t};
            case 3: return {'*', x, c, t};
            case 4: return {'/', x, c, t};
            default: return {'/', c, x, t};
        }
    }
    template <class F> inline void fwd(u64 a, u64 b, F f) const {
        if (a + b <= L) f(a + b);
        if ((u128)a * b <= L) f(a * b);
        if (a > b) { f(a - b); if (a % b == 0) f(a / b); }
        else if (b > a) { f(b - a); if (b % a == 0) f(b / a); }
        else f(1);
    }
    void build(const vector<u64>& pool, u64 limit) {
        L = limit; P = pool; s2built = false;
        Pset.init(128); for (u64 v : P) Pset.insert(v);
        S1.init(P.size() * P.size() * 3 + 64); S1list.clear();
        for (size_t i = 0; i < P.size(); i++)
            for (size_t j = i; j < P.size(); j++)
                fwd(P[i], P[j], [&](u64 r) { if (!Pset.has(r) && S1.insert(r)) S1list.push_back(r); });
        S1sorted = S1list; sort(S1sorted.begin(), S1sorted.end());
    }
    void buildS2() {
        if (s2built) return;
        s2built = true;
        S2.init(S1list.size() * (P.size() + 1) * 3 + 64); S2list.clear();
        auto add = [&](u64 r) { if (!Pset.has(r) && !S1.has(r) && S2.insert(r)) S2list.push_back(r); };
        for (u64 x : S1list) {
            for (u64 c : P) fwd(x, c, add);
            fwd(x, x, add);
        }
    }
    bool d1(u64 t, Plan& p) const {
        u64 x[6]; int k[6];
        for (u64 c : P) {
            int n = invs(t, c, x, k);
            for (int i = 0; i < n; i++) if (Pset.has(x[i])) { p.push_back(fin(k[i], x[i], c, t)); return true; }
        }
        return false;
    }
    bool selfForms(u64 t, u64& x, char& op, const HSet& S) const {
        if (t % 2 == 0 && S.has(t / 2)) { x = t / 2; op = '+'; return true; }
        u64 r = isqrt(t);
        if (r > 1 && r * r == t && S.has(r)) { x = r; op = '*'; return true; }
        return false;
    }
    bool d2(u64 t, Plan& p) const {
        u64 x[6]; int k[6];
        for (u64 c : P) {
            int n = invs(t, c, x, k);
            for (int i = 0; i < n; i++) if (S1.has(x[i])) { d1(x[i], p); p.push_back(fin(k[i], x[i], c, t)); return true; }
        }
        u64 y; char op;
        if (selfForms(t, y, op, S1)) { d1(y, p); p.push_back({op, y, y, t}); return true; }
        return false;
    }
    bool d3(u64 t, Plan& p) const {
        u64 x[6]; int k[6]; u64 x2[6]; int k2[6];
        // tree: t = x o y, both one step from the pool
        for (u64 a : S1list) {
            int n = invs(t, a, x, k);
            for (int i = 0; i < n; i++) if (S1.has(x[i])) {
                d1(a, p); if (x[i] != a) d1(x[i], p);
                p.push_back(fin(k[i], x[i], a, t)); return true;
            }
        }
        // chain: t = x o c, x two steps from the pool
        for (u64 c : P) {
            int n = invs(t, c, x, k);
            for (int i = 0; i < n; i++) {
                size_t m = p.size();
                if (d2(x[i], p)) { p.push_back(fin(k[i], x[i], c, t)); return true; }
                p.resize(m);
            }
        }
        // reuse: t = x o (x o c)
        for (u64 a : S1list) {
            int n = invs(t, a, x, k);
            for (int i = 0; i < n; i++) {
                int n2 = invs(x[i], a, x2, k2);
                for (int j = 0; j < n2; j++) if (Pset.has(x2[j])) {
                    d1(a, p); p.push_back(fin(k2[j], x2[j], a, x[i]));
                    p.push_back(fin(k[i], x[i], a, t)); return true;
                }
            }
        }
        return false;
    }
    bool d4(u64 t, Plan& p) {
        buildS2();
        u64 x[6]; int k[6]; u64 x2[6]; int k2[6];
        for (u64 a : S1list) {
            int n = invs(t, a, x, k);
            for (int i = 0; i < n; i++) if (S2.has(x[i])) {
                d1(a, p); d2(x[i], p); p.push_back(fin(k[i], x[i], a, t)); return true;
            }
        }
        for (u64 c : P) {
            int n = invs(t, c, x, k);
            for (int i = 0; i < n; i++) for (u64 c2 : P) {
                int n2 = invs(x[i], c2, x2, k2);
                for (int j = 0; j < n2; j++) if (S2.has(x2[j])) {
                    d2(x2[j], p); p.push_back(fin(k2[j], x2[j], c2, x[i]));
                    p.push_back(fin(k[i], x[i], c, t)); return true;
                }
            }
        }
        return false;
    }
    bool d5(u64 t, Plan& p) {
        buildS2();
        u64 x[6]; int k[6];
        for (u64 a : S2list) {
            int n = invs(t, a, x, k);
            for (int i = 0; i < n; i++) if (S2.has(x[i])) {
                d2(a, p); if (x[i] != a) d2(x[i], p);
                p.push_back(fin(k[i], x[i], a, t)); return true;
            }
        }
        return false;
    }
    // smallest depth <= maxd that produces v, or -1
    int exact(u64 v, Plan& p, int maxd) {
        if (Pset.has(v)) return 0;
        if (maxd >= 1 && S1.has(v)) { d1(v, p); return 1; }
        if (maxd >= 2 && (s2built ? S2.has(v) : true)) { if (d2(v, p)) return 2; }
        if (maxd >= 3 && d3(v, p)) return 3;
        if (maxd >= 4 && G.effort >= 1 && d4(v, p)) return 4;
        if (maxd >= 5 && G.effort >= 2 && d5(v, p)) return 5;
        return -1;
    }
    // drop steps whose result already exists
    int finalize(Plan& p) const {
        Plan q; unordered_set<u64> seen;
        for (auto& s : p) {
            if (Pset.has(s.res) || seen.count(s.res)) continue;
            seen.insert(s.res); q.push_back(s);
        }
        p.swap(q); return (int)p.size();
    }

    // ---- shared hidden values: values within two inverse steps of several targets ----
    struct Vote { u64 key; int last; short cnt, ksum, kcur; };
    vector<Vote> vt; u64 vmask = 0; int vshift = 0; vector<u64> vkeys;
    inline void vadd(u64 x, int ti, int k) {
        if (x < 2 || Pset.has(x)) return;
        u64 i = (x * 0x9E3779B97F4A7C15ULL) >> vshift;
        while (vt[i].key && vt[i].key != x) i = (i + 1) & vmask;
        Vote& e = vt[i];
        if (!e.key) { e.key = x; e.last = ti; e.cnt = 1; e.ksum = (short)k; e.kcur = (short)k; vkeys.push_back(x); return; }
        if (e.last != ti) { e.last = ti; e.cnt++; e.ksum += k; e.kcur = (short)k; }
        else if (k < e.kcur) { e.ksum -= (e.kcur - k); e.kcur = (short)k; }
    }
    const Vote* vget(u64 x) const {
        if (vt.empty()) return nullptr;
        u64 i = (x * 0x9E3779B97F4A7C15ULL) >> vshift;
        while (vt[i].key && vt[i].key != x) i = (i + 1) & vmask;
        return vt[i].key ? &vt[i] : nullptr;
    }
    void vote(const vector<u64>& targets) {
        size_t cap = 1 << 23; int b = 23;
        if (vt.size() != cap) vt.assign(cap, Vote{0, 0, 0, 0, 0}); else memset((void*)vt.data(), 0, cap * sizeof(Vote));
        vmask = cap - 1; vshift = 64 - b; vkeys.clear();
        u64 x[6]; int k[6]; u64 x2[6]; int k2[6];
        for (int ti = 0; ti < (int)targets.size(); ti++) {
            u64 t = targets[ti];
            if (vkeys.size() > cap / 2) break;
            auto self = [&](u64 v, int kk) {
                if (v % 2 == 0) vadd(v / 2, ti, kk);
                u64 r = isqrt(v); if (r > 1 && r * r == v) vadd(r, ti, kk);
            };
            self(t, 1);
            for (u64 c : P) {
                int n = invs(t, c, x, k);
                for (int i = 0; i < n; i++) {
                    if (x[i] == t) continue;
                    vadd(x[i], ti, 1);
                    self(x[i], 2);
                    for (u64 c2 : P) {
                        int n2 = invs(x[i], c2, x2, k2);
                        for (int j = 0; j < n2; j++) if (x2[j] != t) vadd(x2[j], ti, 2);
                    }
                }
            }
            for (u64 y : S1list) {
                int n = invs(t, y, x, k);
                for (int i = 0; i < n; i++) if (x[i] != t) vadd(x[i], ti, 2);
            }
        }
    }
    inline int depth2(u64 x) const {
        if (Pset.has(x)) return 0;
        if (S1.has(x)) return 1;
        if (s2built) return S2.has(x) ? 2 : -1;
        Plan tmp; return d2(x, tmp) ? 2 : -1;
    }
    inline void derive(u64 x, Plan& p) const {
        if (Pset.has(x)) return;
        if (S1.has(x)) { d1(x, p); return; }
        d2(x, p);
    }
    // always-succeeding fallback: v = q*b + r with the largest usable b
    void construct(u64 v, Plan& p) {
        Plan e;
        if (exact(v, e, 3) >= 0) { p.insert(p.end(), e.begin(), e.end()); return; }
        u64 b = 0;
        for (u64 x : P) if (x >= 2 && x <= v && x > b) b = x;
        if (b < 2) for (u64 x : S1list) if (x >= 2 && x <= v && x > b) b = x;
        if (b * b > v) { // keep the quotient at least as large as the base
            u64 b2 = 0;
            for (u64 x : P) if (x >= 2 && (u128)x * x <= v && x > b2) b2 = x;
            if (b2 >= 2) b = b2;
        }
        if (b < 2) { // nothing small enough: double-and-add
            if (v % 2 == 0) { construct(v / 2, p); p.push_back({'+', v / 2, v / 2, v}); }
            else { construct(v - 1, p); construct(1, p); p.push_back({'+', v - 1, 1, v}); }
            return;
        }
        bool bInPool = Pset.has(b);
        u64 q = v / b, r = v % b;
        construct(q, p);
        if (!bInPool) d1(b, p);
        if (r == 0) { p.push_back({'*', q, b, v}); return; }
        construct(r, p);
        p.push_back({'*', q, b, v - r});
        p.push_back({'+', v - r, r, v});
    }
    struct Node { u64 v; int g; int parent; char mk; u64 b, c; };
    bool hard(u64 t, Plan& out, double minRate, int maxNodes, double rate) {
        if (G.effort >= 1) buildS2();
        vector<Node> nodes; nodes.push_back({t, 0, -1, 0, 0, 0});
        typedef pair<double, int> QE;
        priority_queue<QE, vector<QE>, greater<QE>> pq;
        pq.push({log2((double)t) / rate, 0});
        unordered_map<u64, int> seen; seen[t] = 0;
        int best = INT_MAX; int expansions = 0;
        auto costOf = [&](u64 x) { return Pset.has(x) ? 0 : 1; };
        while (!pq.empty() && expansions < maxNodes) {
            int idx = pq.top().second; pq.pop();
            Node nd = nodes[idx];
            if (nd.g + 1 >= best) continue;
            if (seen[nd.v] < nd.g) continue;
            expansions++;
            Plan p; int maxd = min(idx == 0 ? 5 : 4, best - nd.g - 1);
            int d = exact(nd.v, p, maxd);
            if (d >= 0) {
                int i = idx;
                while (nodes[i].parent >= 0) {
                    const Node& n = nodes[i]; u64 pv = nodes[n.parent].v;
                    if (n.mk == 'A' || n.mk == 'B') {
                        derive(n.b, p);
                        if (n.c == 0) p.push_back({'*', n.v, n.b, pv});
                        else {
                            derive(n.c, p);
                            u64 m = (n.mk == 'A') ? pv - n.c : pv + n.c;
                            p.push_back({'*', n.v, n.b, m});
                            if (n.mk == 'A') p.push_back({'+', m, n.c, pv}); else p.push_back({'-', m, n.c, pv});
                        }
                    } else if (n.mk == 'N' || n.mk == 'O') {
                        derive(n.c, p);
                        u64 m = (n.mk == 'N') ? pv - n.v : pv + n.v;
                        p.push_back({'*', n.c, n.b, m});
                        if (n.mk == 'N') p.push_back({'+', m, n.v, pv}); else p.push_back({'-', m, n.v, pv});
                    } else if (n.mk == 'Q') {
                        p.push_back({'*', n.v, n.v, pv});
                    } else if (n.mk == 'H') {
                        p.push_back({'+', n.v, n.v, pv});
                    } else {
                        derive(n.b, p);
                        if (n.mk == 'C') p.push_back({'+', n.v, n.b, pv}); else p.push_back({'-', n.b, n.v, pv});
                    }
                    i = n.parent;
                }
                int c = finalize(p);
                if (c < best) { best = c; out = p; }
                if (d <= 1) continue;
            }
            if (nd.g + 2 >= best) continue;
            double vb = log2((double)nd.v);
            auto child = [&](u64 cv, char mk, u64 b, u64 c, int cost) {
                if (cv == 0 || cv >= nd.v) return;
                int g = nd.g + cost;
                if (g + 1 >= best) return;
                double gain = vb - log2((double)cv);
                if (gain < minRate * cost) return;
                auto it = seen.find(cv);
                if (it != seen.end() && it->second <= g) return;
                seen[cv] = g;
                nodes.push_back({cv, g, idx, mk, b, c});
                pq.push({g + log2((double)cv) / rate, (int)nodes.size() - 1});
            };
            u64 v = nd.v;
            {
                u64 r = isqrt(v);
                if (r > 1 && r * r == v) child(r, 'Q', 0, 0, 1);
                if (v % 2 == 0) child(v / 2, 'H', 0, 0, 1);
            }
            for (u64 b : P) {
                if (b < 2 || b > v) continue;
                u64 q0 = v / b, r = v % b;
                if (r == 0) { child(q0, 'A', b, 0, 1); }
                else {
                    int dr = depth2(r);
                    if (dr >= 0) child(q0, 'A', b, r, dr + 2);
                    if (q0 >= 2) { int dq = depth2(q0); if (dq >= 0) child(r, 'N', b, q0, dq + 2); }
                    u64 r1 = b - r;
                    if (v + r1 <= L) {
                        int dr1 = depth2(r1);
                        if (dr1 >= 0) child(q0 + 1, 'B', b, r1, dr1 + 2);
                        int dq1 = depth2(q0 + 1);
                        if (dq1 >= 0) child(r1, 'O', b, q0 + 1, dq1 + 2);
                    }
                }
                for (u64 c : P) {
                    if (c <= b) continue;
                    if (c < v && (v - c) % b == 0) child((v - c) / b, 'A', b, c, 2);
                    if (v + c <= L && (v + c) % b == 0) child((v + c) / b, 'B', b, c, 2);
                }
            }
            for (u64 b : S1list) {
                if (b < 16 || b > v) continue;
                u64 r = v % b;
                if (r == 0) { child(v / b, 'A', b, 0, 2); continue; }
                if (Pset.has(r)) child(v / b, 'A', b, r, 3);
                else if (S1.has(r)) child(v / b, 'A', b, r, 4);
                if (v + (b - r) <= L) {
                    if (Pset.has(b - r)) child(v / b + 1, 'B', b, b - r, 3);
                    else if (S1.has(b - r)) child(v / b + 1, 'B', b, b - r, 4);
                }
            }
            for (u64 a : P) {
                if (a < v) child(v - a, 'C', a, 0, 1);
                else if (a > v) child(a - v, 'D', a, 0, 1);
            }
            if (!S1sorted.empty()) {
                auto it = lower_bound(S1sorted.begin(), S1sorted.end(), v);
                for (int s = 0; s < 4; s++) {
                    if (it + s < S1sorted.end()) { u64 a = *(it + s); if (a > v) child(a - v, 'D', a, 0, 2); }
                    if (it - 1 - s >= S1sorted.begin()) { u64 a = *(it - 1 - s); if (a < v) child(v - a, 'C', a, 0, 2); }
                }
            }
            (void)costOf;
        }
        return best != INT_MAX;
    }
};

struct Inst { char op; int a, b, d; };

struct Puzzle {
    string id, family; vector<u64> start, targets; u64 limit; int nreg;
};

struct Machine {
    int nreg; vector<u64> val; vector<char> def; vector<long> last; vector<int> uses; long clock = 0;
    unordered_map<u64, int> where; vector<Inst> prog;
    void init(const Puzzle& pz) {
        nreg = pz.nreg; val.assign(nreg, 0); def.assign(nreg, 0); last.assign(nreg, 0); uses.assign(nreg, 0);
        for (size_t i = 0; i < pz.start.size(); i++) {
            val[i] = pz.start[i]; def[i] = 1;
            if (!where.count(val[i])) where[val[i]] = (int)i;
        }
    }
    vector<u64> pool() const { vector<u64> p; for (auto& kv : where) p.push_back(kv.first); sort(p.begin(), p.end()); return p; }
    void run(const Plan& plan) {
        for (size_t i = 0; i < plan.size(); i++) {
            const Step& s = plan[i];
            if (where.count(s.res)) continue;
            int ra = where.at(s.a), rb = where.at(s.b);
            unordered_set<u64> need;
            for (size_t j = i + 1; j < plan.size(); j++) { need.insert(plan[j].a); need.insert(plan[j].b); }
            int dst = -1;
            for (int r = 0; r < nreg; r++) if (!def[r]) { dst = r; break; }
            if (dst < 0) {
                // a register holding a duplicate value is free to reuse
                for (int r = 0; r < nreg && dst < 0; r++) if (where.at(val[r]) != r) dst = r;
            }
            if (dst < 0) {
                long bestScore = LONG_MAX;
                for (int r = 0; r < nreg; r++) {
                    if (need.count(val[r])) continue;
                    long sc = last[r] + (val[r] <= (u64)G.small ? G.keepBonus : 0) + (long)(uses[r] * G.useW) - (long)(G.bitW * log2((double)val[r]));
                    if (sc < bestScore) { bestScore = sc; dst = r; }
                }
            }
            if (dst < 0) { fprintf(stderr, "no register available\n"); exit(1); }
            clock++;
            last[ra] = clock; last[rb] = clock; uses[ra]++; uses[rb]++;
            if (def[dst] && where.at(val[dst]) == dst) where.erase(val[dst]);
            val[dst] = s.res; def[dst] = 1; last[dst] = clock; uses[dst] = 0; where[s.res] = dst;
            prog.push_back({s.op, ra, rb, dst});
        }
    }
};

static vector<Inst> solvePuzzle(const Puzzle& pz, Ctx& C, vector<int>& costs) {
    Machine M; M.init(pz);
    set<u64> rem(pz.targets.begin(), pz.targets.end());
    bool primed = false;
    for (u64 s : pz.start) rem.erase(s);
    while (!rem.empty()) {
        C.build(M.pool(), pz.limit);
        Plan plan; bool found = false;
        for (u64 t : rem) { plan.clear(); if (C.d1(t, plan)) { found = true; break; } }
        if (!found && G.vote) {
            vector<u64> tv(rem.begin(), rem.end());
            C.vote(tv);
            double bestR = 1e9; int bestCnt = 0;
            auto consider = [&](u64 v, bool isTarget) {
                const Ctx::Vote* e = C.vget(v);
                int cnt = (e ? e->cnt : 0) + (isTarget ? 1 : 0), ks = e ? e->ksum : 0;
                if (cnt < (isTarget ? 1 : 2)) return;
                Plan p; int d = C.exact(v, p, 3);
                if (d < 0) return;
                double r = (double)(d + ks) / cnt;
                if (r < bestR - 1e-9 || (r < bestR + 1e-9 && cnt > bestCnt)) { bestR = r; bestCnt = cnt; plan = p; found = true; }
            };
            for (u64 t : rem) consider(t, true);
            vector<pair<double, u64>> cand;
            for (u64 key : C.vkeys) {
                const Ctx::Vote* e = C.vget(key);
                if (e->cnt >= 2 && !rem.count(key)) cand.push_back({(double)(e->ksum + 1) / e->cnt, key});
            }
            sort(cand.begin(), cand.end());
            for (size_t i = 0; i < cand.size() && i < (size_t)G.maxCand; i++) {
                if (cand[i].first >= bestR) break;
                consider(cand[i].second, false);
            }
        }
        if (!found && !G.vote) {
            for (int depth = 2; depth <= 3 && !found; depth++) {
                for (u64 t : rem) {
                    plan.clear();
                    bool ok = depth == 2 ? C.d2(t, plan) : C.d3(t, plan);
                    if (ok) { found = true; break; }
                }
            }
        }
        if (!found && !primed && G.prime > 0 && (int)C.P.size() <= G.primeMax) {
            // first hard target: seed the pool with 1, 2, 4, ... so residues become cheap
            primed = true; plan.clear();
            u64 a = C.P[0];
            plan.push_back({'/', a, a, 1});
            u64 x = 1;
            for (int i = 0; i < G.prime && x * 2 <= pz.limit; i++) { plan.push_back({'+', x, x, x * 2}); x *= 2; }
            found = true;
        }
        if (!found) {
            u64 t = *rem.begin(); plan.clear();
            if (!C.hard(t, plan, G.minRate, G.nodes, G.rate)) {
                bool ok = C.hard(t, plan, 0.3, max(2000, G.nodes * 10), 1.0);
                if (!ok) { plan.clear(); C.construct(t, plan); }
            }
        }
        C.finalize(plan);
        size_t before = M.prog.size();
        M.run(plan);
        costs.push_back((int)(M.prog.size() - before));
        for (auto& s : plan) rem.erase(s.res);
    }
    // dead-code elimination: keep only instructions that feed a target
    const vector<Inst>& pr = M.prog; int n = (int)pr.size();
    vector<int> writer(pz.nreg, -1), da(n), db(n); vector<u64> val(pz.nreg, 0), res(n);
    for (size_t i = 0; i < pz.start.size(); i++) val[i] = pz.start[i];
    set<u64> need(pz.targets.begin(), pz.targets.end());
    for (u64 s : pz.start) need.erase(s);
    vector<char> live(n, 0);
    for (int i = 0; i < n; i++) {
        da[i] = writer[pr[i].a]; db[i] = writer[pr[i].b];
        u64 a = val[pr[i].a], b = val[pr[i].b], r = 0;
        switch (pr[i].op) { case '+': r = a + b; break; case '-': r = a - b; break; case '*': r = a * b; break; default: r = a / b; }
        res[i] = r; val[pr[i].d] = r; writer[pr[i].d] = i;
        if (need.erase(r)) live[i] = 1;
    }
    for (int i = n - 1; i >= 0; i--) if (live[i]) { if (da[i] >= 0) live[da[i]] = 1; if (db[i] >= 0) live[db[i]] = 1; }
    vector<Inst> out;
    for (int i = 0; i < n; i++) if (live[i]) out.push_back(pr[i]);
    return out;
}

// ---------- CSV ----------
static vector<string> splitCSV(const string& line) {
    vector<string> out; string cur; bool q = false;
    for (char ch : line) {
        if (ch == '"') q = !q;
        else if (ch == ',' && !q) { out.push_back(cur); cur.clear(); }
        else cur += ch;
    }
    out.push_back(cur); return out;
}
static vector<u64> parseList(const string& s) {
    vector<u64> v; u64 cur = 0; bool in = false;
    for (char ch : s) {
        if (isdigit((unsigned char)ch)) { cur = cur * 10 + (ch - '0'); in = true; }
        else { if (in) v.push_back(cur); cur = 0; in = false; }
    }
    if (in) v.push_back(cur);
    return v;
}

int main(int argc, char** argv) {
    if (argc < 3) { fprintf(stderr, "usage: solver puzzles.csv out.csv [options]\n"); return 1; }
    int threads = 2; string only;
    for (int i = 3; i < argc; i++) {
        string a = argv[i];
        auto nxt = [&]() { return string(argv[++i]); };
        if (a == "--threads") threads = stoi(nxt());
        else if (a == "--nodes") G.nodes = stoi(nxt());
        else if (a == "--effort") G.effort = stoi(nxt());
        else if (a == "--rate") G.rate = stod(nxt());
        else if (a == "--minrate") G.minRate = stod(nxt());
        else if (a == "--small") G.small = stoi(nxt());
        else if (a == "--bonus") G.keepBonus = stoi(nxt());
        else if (a == "--only") only = nxt();
        else if (a == "--vote") G.vote = stoi(nxt());
        else if (a == "--usew") G.useW = stod(nxt());
        else if (a == "--bitw") G.bitW = stod(nxt());
        else if (a == "--prime") G.prime = stoi(nxt());
        else if (a == "--primemax") G.primeMax = stoi(nxt());
        else if (a == "--maxcand") G.maxCand = stoi(nxt());
    }
    ifstream in(argv[1]); string line; getline(in, line);
    vector<string> hdr = splitCSV(line);
    map<string, int> col; for (size_t i = 0; i < hdr.size(); i++) { string h = hdr[i]; while (!h.empty() && (h.back() == '\r' || h.back() == '\n')) h.pop_back(); col[h] = (int)i; }
    vector<Puzzle> pzs;
    while (getline(in, line)) {
        if (line.empty()) continue;
        auto f = splitCSV(line);
        Puzzle p; p.id = f[col["id"]]; p.start = parseList(f[col["starting_values"]]);
        p.targets = parseList(f[col["targets"]]); p.limit = stoull(f[col["value_limit"]]);
        p.nreg = col.count("registers") ? stoi(f[col["registers"]]) : NREG_DEFAULT;
        p.family = col.count("family") ? f[col["family"]] : "";
        if (!only.empty() && p.id != only) continue;
        pzs.push_back(p);
    }
    vector<vector<Inst>> progs(pzs.size()); vector<vector<int>> costs(pzs.size());
    atomic<size_t> nextIdx(0);
    auto worker = [&]() {
        Ctx C;
        while (true) {
            size_t i = nextIdx++; if (i >= pzs.size()) break;
            progs[i] = solvePuzzle(pzs[i], C, costs[i]);
        }
    };
    vector<thread> th; for (int i = 0; i < threads; i++) th.emplace_back(worker);
    for (auto& t : th) t.join();
    ofstream out(argv[2]); out << "id,program\n";
    map<string, long> famTotal, famTargets; long total = 0;
    for (size_t i = 0; i < pzs.size(); i++) {
        out << pzs[i].id << ",\"[";
        for (size_t j = 0; j < progs[i].size(); j++) {
            const Inst& s = progs[i][j];
            if (j) out << ", ";
            out << "[\"\"" << s.op << "\"\", " << s.a << ", " << s.b << ", " << s.d << "]";
        }
        out << "]\"\n";
        total += progs[i].size(); famTotal[pzs[i].family] += progs[i].size(); famTargets[pzs[i].family] += costs[i].size();
    }
    for (auto& kv : famTotal) fprintf(stderr, "%-15s %7ld instr  %5ld targets  %.2f/target\n", kv.first.c_str(), kv.second, famTargets[kv.first], (double)kv.second / max(1L, famTargets[kv.first]));
    fprintf(stderr, "TOTAL %ld\n", total);
    if (!only.empty()) for (size_t i = 0; i < pzs.size(); i++) { for (int c : costs[i]) fprintf(stderr, "%d ", c); fprintf(stderr, "\n"); }
    return 0;
}
