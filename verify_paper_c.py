#!/usr/bin/env python3
"""Exact symbolic and finite numerical sanity checks for Paper C.

Scope: checks all elementary algebraic identities, constructive finite-field
Stepanov polynomial solver and admissible parameter bound, Legendre factorial
valuation, rational product formula, divisibility/modulus facts, exact rational
remainder cancellation eq:rem_id, scale-inequality margins and absorption
threshold, Cauchy-moment window bounds, exhaustive Behrend sphere triples, and
CM formal-group prime-sum equivalences stated in paper_c.tex.
"""
from fractions import Fraction as F
from math import ceil, gcd, isqrt, log, sqrt
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
REPORT = {}


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            return False
    return True


def legendre(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return -1 if r == p - 1 else r


def kronecker_neg_d(d: int, n: int) -> int:
    """Exact Kronecker symbol chi_K(n) = (-d / n) for odd prime d == 7 mod 8."""
    assert d % 8 == 7 and is_prime(d) and n >= 1
    out = 1
    m = n
    # At p = 2, (-d / 2) = (-1)^(((-d)^2 - 1) / 8) = (-1)^((d^2 - 1) / 8).
    chi2 = 1 if ((d * d - 1) // 8) % 2 == 0 else -1
    assert chi2 == 1  # holds whenever d == 7 mod 8
    while m % 2 == 0:
        out *= chi2
        m //= 2
    p = 3
    while p * p <= m:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if p == d:
                return 0
            if e % 2 == 1:
                # By quadratic reciprocity for d == 3 mod 4: (-d / p) = (p / d).
                out *= legendre(p, d)
        p += 2
    if m > 1:
        if m == d:
            return 0
        out *= legendre(m, d)
    return out


def check_toy_stepanov():
    """Construct an explicit nonzero Stepanov polynomial for y^2 = x^3 + x + 1 over F_101
    and verify the admissible odd parameter optimization m <= sqrt((p-5)/3)."""
    p = 101
    f_poly = [1, 1, 0, 1]
    d = 3
    m = 5
    K = (m + 1) // 2  # 3
    J = (3 * m * m + m) // 2 + 1  # 41
    assert 3 * m * m + m + 5 <= p
    assert 2 * J + d - 2 < p

    def poly_eval(poly, x):
        acc = 0
        for c in reversed(poly):
            acc = (acc * x + c) % p
        return acc

    def poly_mul(a, b):
        out = [0] * (len(a) + len(b) - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    out[i + j] = (out[i + j] + ai * bj) % p
        return out

    def poly_deriv(a):
        return [(i * a[i]) % p for i in range(1, len(a))]

    def poly_add(a, b):
        n = max(len(a), len(b))
        return [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p for i in range(n)]

    def poly_scale(a, c):
        return [(x * c) % p for x in a]

    f_prime = poly_deriv(f_poly)
    inv2 = (p + 1) // 2

    S0, S_plus, S_minus = [], [], []
    for x in range(p):
        fx = poly_eval(f_poly, x)
        if fx == 0:
            S0.append(x)
        elif legendre(fx, p) == 1:
            S_plus.append(x)
        else:
            S_minus.append(x)
    N_proj = 1 + len(S0) + 2 * len(S_plus)
    assert len(S0) + len(S_plus) + len(S_minus) == p

    n_vars = 2 * J * K
    A_cur = [[0] * j + [1] for j in range(J)]
    B_cur = [[0] * j + [1] for j in range(J)]
    rows = []
    for r in range(m):
        deg_q = (d - 1) * r + J + K - 2
        row_block = [[0] * n_vars for _ in range(deg_q + 1)]
        for j in range(J):
            for k in range(K):
                col_a = j * K + k
                for deg_x, coeff in enumerate(A_cur[j]):
                    if coeff:
                        row_block[deg_x + k][col_a] = (row_block[deg_x + k][col_a] + coeff) % p
                col_b = J * K + j * K + k
                for deg_x, coeff in enumerate(B_cur[j]):
                    if coeff:
                        row_block[deg_x + k][col_b] = (row_block[deg_x + k][col_b] + coeff) % p
        rows.extend(row_block)
        if r + 1 < m:
            next_A, next_B = [], []
            c_a = (-r) % p
            c_b = (-(r + inv2)) % p
            for j in range(J):
                next_A.append(poly_add(
                    poly_mul(f_poly, poly_deriv(A_cur[j])),
                    poly_scale(poly_mul(f_prime, A_cur[j]), c_a),
                ))
                next_B.append(poly_add(
                    poly_mul(f_poly, poly_deriv(B_cur[j])),
                    poly_scale(poly_mul(f_prime, B_cur[j]), c_b),
                ))
            A_cur, B_cur = next_A, next_B

    n_eqs = len(rows)
    assert n_eqs == 235 and n_vars == 246 and n_eqs < n_vars

    mat = [row[:] for row in rows]
    pivots = []
    r_idx = 0
    for c_idx in range(n_vars):
        piv = next((i for i in range(r_idx, n_eqs) if mat[i][c_idx] != 0), None)
        if piv is None:
            continue
        mat[r_idx], mat[piv] = mat[piv], mat[r_idx]
        inv_p = pow(mat[r_idx][c_idx], p - 2, p)
        mat[r_idx] = [(v * inv_p) % p for v in mat[r_idx]]
        for i in range(n_eqs):
            if i != r_idx and mat[i][c_idx] != 0:
                factor = mat[i][c_idx]
                row_i, row_r = mat[i], mat[r_idx]
                for c2 in range(c_idx, n_vars):
                    row_i[c2] = (row_i[c2] - factor * row_r[c2]) % p
        pivots.append(c_idx)
        r_idx += 1

    pivot_set = set(pivots)
    free_cols = [c for c in range(n_vars) if c not in pivot_set]
    assert len(free_cols) >= n_vars - n_eqs
    free_col = free_cols[0]
    sol = [0] * n_vars
    sol[free_col] = 1
    for i, c_idx in enumerate(pivots):
        sol[c_idx] = (-mat[i][free_col]) % p
    assert any(sol)

    def poly_pow(base, exp):
        res, cur, e = [1], base[:], exp
        while e > 0:
            if e & 1:
                res = poly_mul(res, cur)
            cur = poly_mul(cur, cur)
            e >>= 1
        return res

    f_half = poly_pow(f_poly, (p - 1) // 2)
    deg_max = (K - 1) * p + (J - 1) + d * ((p - 1) // 2)
    P_poly = [0] * (deg_max + 1)
    for j in range(J):
        for k in range(K):
            a_jk = sol[j * K + k]
            if a_jk:
                P_poly[j + k * p] = (P_poly[j + k * p] + a_jk) % p
            b_jk = sol[J * K + j * K + k]
            if b_jk:
                shift = j + k * p
                for deg_f, cf in enumerate(f_half):
                    if cf:
                        P_poly[shift + deg_f] = (P_poly[shift + deg_f] + b_jk * cf) % p
    while len(P_poly) > 1 and P_poly[-1] == 0:
        P_poly.pop()
    actual_deg = len(P_poly) - 1
    assert 0 < actual_deg <= deg_max

    cur_deriv = P_poly[:]
    for r in range(m):
        for x0 in S_plus:
            assert poly_eval(cur_deriv, x0) == 0, (r, x0)
        cur_deriv = poly_deriv(cur_deriv)

    assert m * len(S_plus) <= actual_deg
    stepanov_upper = F(p, 2) + F(p, m) + F(3 * m + 1, 2)
    assert len(S_plus) <= stepanov_upper
    assert abs(N_proj - (p + 1)) <= F(2 * p, m) + 3 * m + 4

    # Three-root cubic check: f(x) = x(x-1)(x-2) mod 101
    f_split = [0, 2, p - 3, 1]
    s0_cnt = sum(1 for x in range(p) if poly_eval(f_split, x) == 0)
    sp_cnt = sum(1 for x in range(p) if legendre(poly_eval(f_split, x), p) == 1)
    sm_cnt = sum(1 for x in range(p) if legendre(poly_eval(f_split, x), p) == -1)
    assert s0_cnt == 3 and s0_cnt + sp_cnt + sm_cnt == p
    assert sp_cnt <= stepanov_upper and sm_cnt <= stepanov_upper
    assert abs((1 + s0_cnt + 2 * sp_cnt) - (p + 1)) <= F(2 * p, m) + 3 * m + 4

    # Admissible optimal odd m check across p = 101, 10007, 100003: ratio -> 3*sqrt(3)
    opt_checks = []
    for q_prime in (101, 10007, 100003):
        m_opt = 1
        while 3 * (m_opt + 2) ** 2 + (m_opt + 2) + 5 <= q_prime:
            m_opt += 2
        assert 3 * m_opt * m_opt + m_opt + 5 <= q_prime
        assert 3 * (m_opt + 2) ** 2 + (m_opt + 2) + 5 > q_prime
        ratio = (2 * q_prime / m_opt + 3 * m_opt + 4) / sqrt(q_prime)
        opt_checks.append({"p": q_prime, "m_max_odd": m_opt, "bound_over_sqrt_p": round(ratio, 4)})
    assert abs(opt_checks[-1]["bound_over_sqrt_p"] - 3.0 * sqrt(3.0)) < 0.1

    REPORT["toy_stepanov_F101"] = {
        "prime_p": p,
        "curve": "y^2 = x^3 + x + 1",
        "m": m,
        "J": J,
        "K": K,
        "unknowns": n_vars,
        "equations": n_eqs,
        "S0_count": len(S0),
        "S_plus_count": len(S_plus),
        "S_minus_count": len(S_minus),
        "N_projective": N_proj,
        "actual_deg_P": actual_deg,
        "max_deg_P": deg_max,
        "stepanov_S_plus_bound": float(stepanov_upper),
        "all_S_plus_roots_order_m_verified": True,
        "three_root_cubic_checked": {"S0": s0_cnt, "S_plus": sp_cnt, "S_minus": sm_cnt},
        "admissible_optimal_m_ratios": opt_checks,
        "asymptotic_constant_3sqrt3": round(3.0 * sqrt(3.0), 6),
    }


def check_product_formula_and_legendre():
    """Verify worked rational product formula (12/35) and Legendre's formula."""
    q = F(12, 35)
    vals = {2: 2, 3: 1, 5: -1, 7: -1}
    prod_val = q
    log_sum = log(float(q))
    for p, vp in vals.items():
        padic_abs = F(1, p ** vp) if vp >= 0 else F(p ** (-vp), 1)
        prod_val *= padic_abs
        log_sum += -vp * log(p)
    assert prod_val == 1 and abs(log_sum) < 1e-14

    def vp_fact(n, p):
        s, pe = 0, p
        while pe <= n:
            s += n // pe
            pe *= p
        return s

    def digit_sum(n, p):
        s = 0
        while n > 0:
            s += n % p
            n //= p
        return s

    for p in (2, 3, 5, 7, 13, 17):
        for n in (10, 50, 200, 1000):
            lhs = vp_fact(n, p)
            rhs_exact = (n - digit_sum(n, p)) // (p - 1)
            assert lhs == rhs_exact
            assert (n - digit_sum(n, p)) % (p - 1) == 0
    REPORT["product_formula_and_legendre"] = {
        "worked_rational": "12/35",
        "product_equals_one": True,
        "v_13_of_1000_fact": vp_fact(1000, 13),
        "legendre_exact_pairs_checked": 24,
    }


def check_modulus_and_splitting():
    """Verify 18480 | q_0, 5040 | 3*q_0, d == 7 mod 8, primes <= 11 split in K,
    and dynamically compute the actual smallest nonsplit prime for each sample d."""
    assert 18480 == 16 * 3 * 5 * 7 * 11
    assert (18480 * 3) % 5040 == 0
    first_prime_q1 = None
    first_nonsplit_for_q1 = None
    min_nonsplit_observed = None
    checked_pairs = 0
    for q in (1, 2, 3, 5, 7, 12):
        q0 = 18480 * q
        d0 = q0 // 2 - 1
        assert gcd(d0, q0) == 1
        assert (d0 * d0) % q0 == 1
        assert d0 % 8 == 7
        d = d0
        while not is_prime(d):
            d += q0
        if q == 1:
            first_prime_q1 = d
        assert d > 64 and d % 8 == 7
        for p in (2, 3, 5, 7, 11):
            assert kronecker_neg_d(d, p) == 1, (q, d, p)
        # Dynamically locate the smallest nonsplit prime for this d
        p_scan = 2
        while True:
            if is_prime(p_scan) and kronecker_neg_d(d, p_scan) != 1:
                break
            p_scan += 1
        assert p_scan >= 13
        if q == 1:
            first_nonsplit_for_q1 = p_scan
        min_nonsplit_observed = p_scan if min_nonsplit_observed is None else min(min_nonsplit_observed, p_scan)
        checked_pairs += 1
    REPORT["modulus_and_splitting"] = {
        "base_modulus": 18480,
        "first_admissible_prime_for_q1": first_prime_q1,
        "smallest_nonsplit_prime_for_d_9239": first_nonsplit_for_q1,
        "min_nonsplit_prime_observed_across_samples": min_nonsplit_observed,
        "guaranteed_lower_bound_min_nonsplit_prime": 13,
        "stably_unramified_root_order": 5040,
        "base_times_3_div_5040": (18480 * 3) // 5040,
        "sample_q_tested": checked_pairs,
    }


def check_cauchy_window_inequalities():
    """Verify the three-term exponential dominance in the Cauchy-moment window lemma."""
    tested = []
    for R in (3.01, 3.1, 3.5, 3.9):
        t_min = max(9.0, 99.0 / (log(R) - log(3.0)))
        for t in (t_min, 1.5 * t_min, 2.0 * t_min):
            k = ceil(t * t / 9.0)
            assert k < t * t / 9.0 + 1.0
            log_neg = -t - (k + 1) * log(3.0)
            log_t1 = 7.0 * t - (k + 1) * log(R)
            log_t2 = 2.0 * t - t * t
            log_t3 = 2.0 * t - k * log(R)
            rhs = log_neg - log(3.0)
            assert log_t1 < rhs, (R, t, log_t1, rhs)
            assert log_t2 < rhs, (R, t, log_t2, rhs)
            assert log_t3 < rhs, (R, t, log_t3, rhs)
            assert (R - 2.0) * t <= 5.0 * t
            # Also verify the explicit paper bound (k+2)*log(3) <= 1.1*(t^2/9 + 3) < t^2 - 3t
            assert (k + 2) * log(3.0) <= 1.1 * (t * t / 9.0 + 3.0) < t * t - 3.0 * t
        tested.append({"R": R, "t_min": round(t_min, 2)})
    REPORT["cauchy_window_lemma"] = {
        "R_values_checked": tested,
        "all_three_terms_strictly_below_one_third": True,
    }


def check_behrend_sphere():
    """Verify the Behrend sphere construction produces weighted 3-AP-free sets,
    exhaustively testing ALL 9^3 * 3 = 2,187 weighted triples (including e1 == e3)."""
    L, H, n = 3, 5, 3
    base = L * H
    o = base ** n
    spheres = {}
    for d0 in range(H):
        for d1 in range(H):
            for d2 in range(H):
                r2 = d0 * d0 + d1 * d1 + d2 * d2
                val = d0 + base * d1 + base * base * d2
                spheres.setdefault(r2, []).append(val)
    best_r2, S = max(spheres.items(), key=lambda kv: len(kv[1]))
    assert len(S) >= (H ** n) / (n * H * H)
    total_triples = 0
    nontrivial_triples = 0
    for alpha in range(1, L):
        for ap in range(1, L - alpha + 1):
            for e1 in S:
                for e2 in S:
                    for e3 in S:
                        total_triples += 1
                        if ((alpha + ap) * e2) % o == (alpha * e1 + ap * e3) % o:
                            assert e1 == e2 == e3, (alpha, ap, e1, e2, e3)
                        else:
                            nontrivial_triples += 1
    assert total_triples == 3 * (len(S) ** 3)  # (alpha, ap) in {(1,1),(1,2),(2,1)}
    REPORT["behrend_sphere"] = {
        "L": L,
        "H": H,
        "n": n,
        "modulus": o,
        "sphere_radius_sq": best_r2,
        "set_size": len(S),
        "pigeonhole_lower_bound": round((H ** n) / (n * H * H), 3),
        "total_weighted_triples_checked": total_triples,
        "nontrivial_triples_verified_free": nontrivial_triples,
    }


def check_cm_gamma_and_prime_sum():
    """Verify gamma_p = v(pi_p) sum_{e in I_p} p^{-e} and exact symbolic s_fin equivalence."""
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23):
        rho_inert = F(1, p * p - 1)
        gamma_inert = F(1, p - 1) - rho_inert
        assert gamma_inert == F(p, p * p - 1)
        rho_ram = F(1, 2 * (p - 1))
        gamma_ram = F(1, p - 1) - rho_ram
        assert gamma_ram == F(1, 2 * (p - 1))
        assert (p + 1) * rho_inert - 1 + 1 == F(1, p - 1)
        assert (p + 1) * rho_ram - 1 + F(1, 2) == F(1, p - 1)

    # Exact rational per-prime coefficient check (no floating-point rounding)
    d = 71
    y = F(250, 1)

    def kappa(residue_shift: int) -> F:
        return F(5, 2) + F(residue_shift % 7, 2)

    lhs_by_p = {}
    for n in range(2, 251):
        p_found = None
        for p in range(2, n + 1):
            if is_prime(p) and n % p == 0:
                m = n
                while m % p == 0:
                    m //= p
                if m == 1:
                    p_found = p
                break
        if p_found is not None:
            coeff = F(1 - kronecker_neg_d(d, n), 1) * max(y / n - kappa(-n), F(0))
            if coeff:
                lhs_by_p[p_found] = lhs_by_p.get(p_found, F(0)) + coeff

    rhs_by_p = {}
    for p in range(2, 251):
        if not is_prime(p):
            continue
        chi_p = kronecker_neg_d(d, p)
        if chi_p == 1:
            continue
        v_pi = F(1, 2) if p == d else F(1, 1)
        s_p = F(0)
        e, pe = 1, p
        while pe <= 250:
            if (p == d) or (e % 2 == 1):
                s_p += v_pi * max(y / pe - kappa(-pe), F(0))
            e += 1
            pe *= p
        if s_p:
            rhs_by_p[p] = 2 * s_p

    assert lhs_by_p == rhs_by_p
    REPORT["cm_formal_group_prime_sum"] = {
        "primes_checked_exact_series": 9,
        "radius_identity_verified": True,
        "exact_rational_prime_coefficients_matched": len(lhs_by_p),
        "exact_rational_diff": "0",
    }


def check_exact_remainder_identity_and_scales():
    """Exact Fraction verification of eq:rem_id (fiber-counting cancellation over Phi_a)
    and exact dynamic verification of the Main Inequality absorption threshold."""
    # Exact symbolic/rational check of eq:rem_id on a concrete finite group Phi = (Z/q1 Z)^x
    # with q0 = 8, T = 4, q1 = 32 (phi(8) = 4, f = 16, #Phi_a = 4, #Phi_b = 2).
    q0, T = 8, 4
    q1 = q0 * T
    Phi = [u for u in range(1, q1) if gcd(u, q1) == 1]
    phi_q0 = sum(1 for u in range(1, q0) if gcd(u, q0) == 1)
    assert len(Phi) == phi_q0 * T
    Phi_a = [u for u in Phi if u % q0 == 1]
    Phi_neg = [u for u in Phi if u % q0 == q0 - 1]
    Phi_b = Phi_neg[:2]  # subset of {-1 mod q0}
    assert len(Phi_a) == T and len(Phi_b) == 2

    # Choose arbitrary exact rational values for a, x, x1, log_a, log_x, log_x1, C_CS, c_q0, and weights lam(n)
    x = F(10, 1)
    x1 = F(25, 1)
    a = F(50, 1)
    kappa_map = {s: (a / x if s in Phi_b else a / x1) for s in Phi}

    # Exact linear symbols: use rational basis vectors to check exact cancellation of EVERY symbol
    # Basis: 0..50 for lam(1..50), 51 for log(a), 52 for log(x), 53 for log(x1), 54 for C_CS, 55 for c_q0
    # Note: c_1 = -1 - C_CS, and log(kappa(s)) = log(a) - log(x) (Phi_b) or log(a) - log(x1) (else).
    # In exact rational arithmetic, evaluate with distinct primes/independently varied rational scalars
    # AND verify the exact coefficient vector of every term vanishes identically.
    N_max = 50
    # Verify exact coefficient of each symbol: [lam(1)..lam(N_max), 1, log_a, log_x, log_x1, C_CS, c_q0]
    dim = N_max + 6
    IDX_ONE = N_max
    IDX_LOGA = N_max + 1
    IDX_LOGX = N_max + 2
    IDX_LOGX1 = N_max + 3
    IDX_CCS = N_max + 4
    IDX_CQ0 = N_max + 5

    # Only units mod q1 (or primes not dividing q1) appear with nonzero weight in the paper;
    # test all integers 1 <= nu <= N_max with gcd(nu, q1) == 1 (all primes dividing q1 split in K, so lam=0 there).
    def vec_zero():
        return [F(0)] * dim

    def vec_add(u, v, scale=F(1)):
        return [ui + scale * vi for ui, vi in zip(u, v)]

    # Build mean log(kappa) = (1/f) * sum_{s in Phi} log(kappa(s))
    f_card = len(Phi)
    mean_log_kappa = vec_zero()
    mean_log_kappa[IDX_LOGA] = F(1)
    mean_log_kappa[IDX_LOGX] = F(-len(Phi_b), f_card)
    mean_log_kappa[IDX_LOGX1] = F(-(f_card - len(Phi_b)), f_card)

    # s_main = a * (log_a - mean_log_kappa - 1 - C_CS)
    s_main = vec_zero()
    s_main[IDX_LOGA] = a
    s_main = vec_add(s_main, mean_log_kappa, -a)
    s_main[IDX_ONE] -= a
    s_main[IDX_CCS] -= a

    # LHS: rem = sum_{tau in Phi_a} (s_fin(a, tau) - s_main)
    lhs = vec_zero()
    for tau in Phi_a:
        for nu in range(1, N_max + 1):
            if gcd(nu, q1) != 1:
                continue
            partner = (-nu * tau) % q1
            diff = a / nu - kappa_map[partner]
            if diff > 0:
                lhs[nu - 1] += diff
        lhs = vec_add(lhs, s_main, F(-1))

    # RHS: a * #Phi_b * (R_{q0}(x) - R_{q0}(x1) + (#Phi_a / #Phi_b) * R_1(x1))
    def R_vec(mod_q, cutoff):
        v = vec_zero()
        for nu in range(1, N_max + 1):
            if gcd(nu, q1) != 1:
                continue
            if nu <= cutoff and (nu % mod_q == 1 % mod_q):
                v[nu - 1] += F(1, nu) - F(1) / cutoff
        phi_m = phi_q0 if mod_q == q0 else 1
        idx_log = IDX_LOGX if cutoff == x else IDX_LOGX1
        v[idx_log] -= F(1, phi_m)
        if mod_q == q0:
            v[IDX_CQ0] -= F(1)
        else:
            # c_1 = -1 - C_CS => -c_1 = +1 + C_CS
            v[IDX_ONE] += F(1)
            v[IDX_CCS] += F(1)
        return v

    rhs = vec_zero()
    rhs = vec_add(rhs, R_vec(q0, x), a * len(Phi_b))
    rhs = vec_add(rhs, R_vec(q0, x1), -a * len(Phi_b))
    rhs = vec_add(rhs, R_vec(1, x1), a * len(Phi_a))
    assert lhs == rhs

    # Scale parity & GRH epsilon margins
    for er in range(1, 6):
        r = 3 ** (er + 1)
        for em in range(1, 4):
            m = 2 ** (em + 1)
            if m < r:
                k = r + 1 - m
                assert k % 2 == 0, (r, m, k)
                z_lo = 7 * (m // 2)
                z_hi = z_lo + k // 2
                assert 2 * (z_hi - z_lo) == k
                if r >= 6 * m + 1:
                    assert z_lo > m and z_hi <= r, (r, m, z_lo, z_hi)
    assert F(1, 2) - 8 * F(1, 100) == F(21, 50) > 0
    for re_rho in (F(51, 100), F(3, 5), F(3, 4), F(1, 1), F(2, 1)):
        eps = (min(re_rho, F(1)) - F(1, 2)) / 51
        assert F(0) < eps < F(1, 100)
        beta = F(1, 2) + 8 * eps
        assert F(1, 2) < beta < re_rho

    # Verify the (*) absorption inequality
    #   4*L_cov + 4*x^99 + 10*log(1 + b^2)*B <= f*a*(log b)^5
    # under Table 2's full admissible tower:
    #   x^{10^6} <= x_1, x_1^{10^6} <= b  =>  x^{10^{12}} <= b,
    #   (log b)^{100} <= x,  a >= x*b,  f >= 1,  B = f*a*(log b)^3,  L_cov = f*a*(log b)^4.
    # Dividing by B = f*a*(log b)^3 gives:
    #   4*log b + 4*x^99/(f*a*(log b)^3) + 10*log(1 + b^2) <= (log b)^2.
    # Under x^{10^{12}} <= b and a >= x*b, 4*x^99/(f*a*(log b)^3) <= 4*x^98/(b*(log b)^3)
    # <= 4*b^(98e-12 - 1)/(log b)^3 << 1.
    # Test concrete admissible-tower corners in log10 space (exact float comparison):
    import math as _m
    LN10 = _m.log(10.0)
    tower_margins = {}
    for log_b in (1e16, 1e18, 1e24):
        # Upper-bound x from x <= b^{10^{-12}} (consistent with (log b)^{100} <= x for log_b >= 4e15)
        log_x = 1e-12 * log_b
        assert 100.0 * _m.log(log_b) <= log_x, (log_b, log_x)
        # log10(4 * x^99 / B) <= log10(4) + 98*log_x/LN10 - log_b/LN10 - 3*log10(log_b)
        log10_x99_over_B = _m.log10(4.0) + (98.0 * log_x - log_b) / LN10 - 3.0 * _m.log10(log_b)
        assert log10_x99_over_B < -1e14
        # Remaining terms divided by B: 4*log_b + 10*log(1 + b^2) < 24*log_b + 1 < (log_b)^2 - 1
        rem_ratio = (4.0 * log_b + 20.0 * log_b + 1.0) / (log_b * log_b)
        assert rem_ratio < 1e-12
        tower_margins[f"log_b={log_b:.0e}"] = {
            "log10_4x99_over_B_upper": round(log10_x99_over_B, 2),
            "non_x99_over_rhs_upper": rem_ratio,
        }

    # Regression check: the reduced quadratic g(u) = u^2 - 4u - 10*log(1 + e^{2u})
    # ONLY governs the non-x^99 terms (root near 24.000); at the inadmissible corner
    # (log b = 25, x = 25^{100}), 4*x^99 massively exceeds f*a*(log b)^5, proving
    # that the full tower x^{10^{12}} <= b (not just (log b)^{100} <= x) is essential.
    lo, hi = 23.0, 26.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        val = mid * mid - 4.0 * mid - 10.0 * (2.0 * mid + log(1.0 + pow(2.718281828459045, -2.0 * mid)))
        if val <= 0.0:
            lo = mid
        else:
            hi = mid
    reduced_quad_root = hi
    assert 24.0 < reduced_quad_root < 24.01
    # Corner regression at log_b = 25, x = 25^{100}:
    log10_x_corner = 100.0 * _m.log10(25.0)
    log10_4x99_corner = _m.log10(4.0) + 99.0 * log10_x_corner
    # Lower bound on f*a*(log b)^5 using f >= x^11, a >= x*b:
    log10_rhs_lb_corner = 12.0 * log10_x_corner + 25.0 / LN10 + 5.0 * _m.log10(25.0)
    assert log10_4x99_corner - log10_rhs_lb_corner > 12000.0

    REPORT["scales_and_cancellations"] = {
        "exact_rem_id_finite_instance": {"q0": q0, "T": T, "q1": q1, "symbolic_components": dim},
        "exact_rem_id_matches_identically": True,
        "k_even_for_odd_r_even_m": True,
        "main_pair_doubled_count_equals_k": True,
        "grh_eps_margin_sample_verified": True,
        "star_full_tower_absorption_verified": True,
        "star_tower_margins": tower_margins,
        "reduced_non_x99_quadratic_root": round(reduced_quad_root, 6),
        "dropped_x99_corner_regression_log10_excess": round(log10_4x99_corner - log10_rhs_lb_corner, 1),
    }


def main():
    check_toy_stepanov()
    check_product_formula_and_legendre()
    check_modulus_and_splitting()
    check_cauchy_window_inequalities()
    check_behrend_sphere()
    check_cm_gamma_and_prime_sum()
    check_exact_remainder_identity_and_scales()
    REPORT["status"] = "PASS"
    REPORT["scope"] = (
        "Constructive Stepanov polynomial verification over F_101 plus exact rational "
        "checks of elementary lemmas, finite sanity checks of eq:rem_id and epsilon margins, "
        "and full-tower scale verification of the (*) absorption step."
    )
    (HERE / "verification_results.json").write_text(json.dumps(REPORT, indent=2) + "\n")
    print(json.dumps(REPORT, indent=2))


if __name__ == "__main__":
    main()
