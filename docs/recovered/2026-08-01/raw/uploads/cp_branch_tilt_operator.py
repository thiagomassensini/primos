#!/usr/bin/env python3
"""
Cp Branch + Tilt Operator
=========================

Script auditavel para a parte quadratica da geometria Cp.

Ele implementa tres objetos:

1) Operador de ramo puro

    W_{p,s}: C -> ell^2(A_p x {k0, k0+1, ...})
    (W_{p,s} z)_{a,k} = p^(-k s) z

2) Operador de ramo com coeficientes por perna

    W_{p,s,alpha} z_{a,k} = alpha_a * p^(-k s) z

   A massa quadratica fica:

    ||W_{p,s,alpha}||^2 = (sum_a |alpha_a|^2) * sum_{k>=k0} p^(-2 k sigma)

   Se os coeficientes forem normalizados para energia critica, a saturacao volta a ocorrer
   em sigma = 1/2.

3) Tilt Cp transversal

    delta = sigma - 1/2

    Theta^{(p)}_delta(c)
      = sum_{a in A_p} (c+a)^(-delta) - |A_p| c^(-delta)

   Equivalentemente, para pernas simetricas, e uma soma de segundas diferencas centradas.
   Para sigma > 1/2, o tilt e positivo.
   Para sigma = 1/2, o tilt e zero.
   Para 0 < sigma < 1/2, o tilt e negativo.

Convencoes canonicas:

    p = 2:
        A_2 = {-1, +1}
        k0 = 2

    p impar:
        A_p = {-(p-1)/2, ..., -1, +1, ..., +(p-1)/2}
        k0 = 1

Dependencias: somente biblioteca padrao do Python.
"""

from __future__ import annotations

import argparse
import cmath
import math
from dataclasses import dataclass
from typing import Iterable


EPS = 1e-15


def is_prime(p: int) -> bool:
    """Teste simples de primalidade para primos pequenos/medios."""
    if p < 2:
        return False
    if p == 2:
        return True
    if p % 2 == 0:
        return False
    d = 3
    while d * d <= p:
        if p % d == 0:
            return False
        d += 2
    return True


def parse_int_list(text: str) -> list[int]:
    """Parseia '2,3,5' em [2, 3, 5]."""
    out: list[int] = []
    for part in text.split(','):
        part = part.strip()
        if part:
            out.append(int(part))
    return out


def parse_float_list(text: str) -> list[float]:
    """Parseia '0.25,0.5,1.0' em [0.25, 0.5, 1.0]."""
    out: list[float] = []
    for part in text.split(','):
        part = part.strip()
        if part:
            out.append(float(part))
    return out


def parse_complex(text: str) -> complex:
    """Parseia complexo em formato Python, aceitando 'i' como alias de 'j'."""
    clean = text.strip().replace('i', 'j')
    return complex(clean)


def cp_legs(p: int) -> tuple[int, ...]:
    """Ramos laterais canonicos A_p."""
    if not is_prime(p):
        raise ValueError(f"p precisa ser primo; recebido p={p}")
    if p == 2:
        return (-1, 1)
    h = (p - 1) // 2
    return tuple(range(-h, 0)) + tuple(range(1, h + 1))


def cp_k0(p: int, k_start: int | None = None) -> int:
    """Profundidade inicial canonica."""
    if k_start is not None:
        if k_start < 1:
            raise ValueError("k_start precisa ser >= 1")
        return int(k_start)
    return 2 if p == 2 else 1


def positive_pow(x: float, exponent: float) -> float:
    """Calcula x^exponent para x positivo, de modo estavel."""
    if x <= 0.0:
        raise ValueError(f"base positiva esperada; recebido {x}")
    return math.exp(exponent * math.log(x))


def fmt_complex(z: complex) -> str:
    """Formato compacto para complexos."""
    return f"{z.real: .12e}{z.imag:+.12e}j"


def parse_leg_coefficients(text: str, legs: tuple[int, ...]) -> dict[int, complex]:
    """
    Parseia coeficientes por perna.

    Formatos aceitos:

        "uniform"             -> alpha_a = 1 para todo a
        "-2:1,-1:1,1:1,2:1"   -> coeficientes explicitos
        "-1:1,1:-1"           -> exemplo C2 antissimetrico
        "-2:1,-1:i,1:-i,2:1"  -> complexos aceitando i

    Pernas omitidas recebem 0.
    """
    clean = text.strip()
    if clean.lower() in {"", "uniform", "ones", "1"}:
        return {a: 1.0 + 0.0j for a in legs}

    coeffs = {a: 0.0 + 0.0j for a in legs}
    allowed = set(legs)
    for item in clean.split(','):
        item = item.strip()
        if not item:
            continue
        if ':' not in item:
            raise ValueError(
                "coeficientes precisam ter formato a:valor, ex: -1:1,1:-1"
            )
        a_text, value_text = item.split(':', 1)
        a = int(a_text.strip())
        if a not in allowed:
            raise ValueError(f"perna a={a} nao pertence a A_p={legs}")
        coeffs[a] = parse_complex(value_text.strip())
    return coeffs


@dataclass(frozen=True)
class CpBranchOperator:
    """
    Operador de ramo Cp puro.

    Parameters
    ----------
    p:
        Primo da geometria Cp.
    k_start:
        Profundidade inicial. Se None, usa p=2 -> 2; p impar -> 1.
    """

    p: int
    k_start: int | None = None

    def __post_init__(self) -> None:
        if not is_prime(self.p):
            raise ValueError(f"p precisa ser primo; recebido p={self.p}")
        if self.k_start is not None and self.k_start < 1:
            raise ValueError("k_start precisa ser >= 1")

    @property
    def k0(self) -> int:
        return cp_k0(self.p, self.k_start)

    @property
    def legs(self) -> tuple[int, ...]:
        return cp_legs(self.p)

    @property
    def branch_count(self) -> int:
        return len(self.legs)

    def q_branch(self, sigma: float) -> float:
        """Razao quadratica q_br(sigma)=p^(-2 sigma)."""
        self._check_sigma(sigma)
        return self.p ** (-2.0 * sigma)

    def coefficient(self, k: int, sigma: float, t: float = 0.0) -> complex:
        """Coeficiente p^(-k(sigma+i t))."""
        if k < self.k0:
            raise ValueError(f"k={k} abaixo de k0={self.k0}")
        self._check_sigma(sigma)
        s = complex(sigma, t)
        return cmath.exp(-k * s * math.log(self.p))

    def apply_finite(
        self,
        z: complex,
        sigma: float,
        t: float = 0.0,
        K: int = 12,
    ) -> dict[tuple[int, int], complex]:
        """Aplica W_{p,s} z truncado ate K."""
        if K < self.k0:
            raise ValueError(f"K={K} abaixo de k0={self.k0}")
        out: dict[tuple[int, int], complex] = {}
        for k in range(self.k0, K + 1):
            coeff = self.coefficient(k, sigma=sigma, t=t)
            for a in self.legs:
                out[(a, k)] = coeff * z
        return out

    def finite_mass(self, sigma: float, K: int) -> float:
        """Massa quadratica truncada ate K."""
        if K < self.k0:
            return 0.0
        q = self.q_branch(sigma)
        n_terms = K - self.k0 + 1
        if abs(1.0 - q) < EPS:
            return self.branch_count * n_terms
        return self.branch_count * (q ** self.k0) * (1.0 - q ** n_terms) / (1.0 - q)

    def tail_mass(self, sigma: float, K: int) -> float:
        """Cauda quadratica depois de K."""
        self._check_sigma(sigma)
        q = self.q_branch(sigma)
        if K < self.k0:
            return self.mass(sigma)
        return self.branch_count * (q ** (K + 1)) / (1.0 - q)

    def mass(self, sigma: float) -> float:
        """Norma quadratica infinita ||W_{p,s}||^2."""
        self._check_sigma(sigma)
        q = self.q_branch(sigma)
        return self.branch_count * (q ** self.k0) / (1.0 - q)

    def norm(self, sigma: float) -> float:
        """Norma ||W_{p,s}||."""
        return math.sqrt(self.mass(sigma))

    def defect(self, sigma: float) -> float:
        """Defeito de ramo: mass - 1."""
        return self.mass(sigma) - 1.0

    def regime(self, sigma: float, tol: float = 1e-12) -> str:
        """Classifica contracao / saturacao / expansao."""
        d = self.defect(sigma)
        if abs(d) <= tol:
            return "saturacao"
        if d < 0:
            return "contracao"
        return "expansao"

    def check_tail_identity(self, sigma: float, K: int) -> float:
        """Erro de finite_mass + tail_mass = mass."""
        return abs(self.finite_mass(sigma, K) + self.tail_mass(sigma, K) - self.mass(sigma))

    def _check_sigma(self, sigma: float) -> None:
        if sigma <= 0.0:
            raise ValueError("sigma precisa ser > 0 para a massa infinita convergir")


@dataclass(frozen=True)
class CpWeightedBranchOperator:
    """
    Operador de ramo Cp com coeficientes por perna.

    (W_{p,s,alpha} z)_{a,k} = alpha_a * p^(-k s) z

    A massa quadratica depende apenas da energia dos coeficientes:

        E_alpha = sum_a |alpha_a|^2.
    """

    p: int
    coefficients: dict[int, complex]
    k_start: int | None = None

    def __post_init__(self) -> None:
        if not is_prime(self.p):
            raise ValueError(f"p precisa ser primo; recebido p={self.p}")
        legs = cp_legs(self.p)
        extra = set(self.coefficients) - set(legs)
        if extra:
            raise ValueError(f"coeficientes possuem pernas invalidas: {sorted(extra)}")
        if self.k_start is not None and self.k_start < 1:
            raise ValueError("k_start precisa ser >= 1")

    @property
    def k0(self) -> int:
        return cp_k0(self.p, self.k_start)

    @property
    def legs(self) -> tuple[int, ...]:
        return cp_legs(self.p)

    @property
    def energy(self) -> float:
        return sum(abs(self.coefficients.get(a, 0.0 + 0.0j)) ** 2 for a in self.legs)

    @property
    def critical_energy(self) -> float:
        """
        Energia necessaria para mass(1/2)=1.

        E * q^k0/(1-q) = 1, com q=p^(-1).
        """
        q = 1.0 / float(self.p)
        return (1.0 - q) / (q ** self.k0)

    def normalized(self) -> "CpWeightedBranchOperator":
        """Retorna uma copia com energia escalada para saturar em sigma=1/2."""
        e = self.energy
        if e <= 0.0:
            raise ValueError("nao da para normalizar coeficientes com energia zero")
        scale = math.sqrt(self.critical_energy / e)
        return CpWeightedBranchOperator(
            p=self.p,
            k_start=self.k_start,
            coefficients={a: self.coefficients.get(a, 0.0 + 0.0j) * scale for a in self.legs},
        )

    def q_branch(self, sigma: float) -> float:
        if sigma <= 0.0:
            raise ValueError("sigma precisa ser > 0 para a massa infinita convergir")
        return self.p ** (-2.0 * sigma)

    def coefficient(self, a: int, k: int, sigma: float, t: float = 0.0) -> complex:
        if a not in self.legs:
            raise ValueError(f"a={a} nao pertence a A_p={self.legs}")
        if k < self.k0:
            raise ValueError(f"k={k} abaixo de k0={self.k0}")
        s = complex(sigma, t)
        return self.coefficients.get(a, 0.0 + 0.0j) * cmath.exp(-k * s * math.log(self.p))

    def apply_finite(
        self,
        z: complex,
        sigma: float,
        t: float = 0.0,
        K: int = 12,
    ) -> dict[tuple[int, int], complex]:
        if K < self.k0:
            raise ValueError(f"K={K} abaixo de k0={self.k0}")
        out: dict[tuple[int, int], complex] = {}
        for k in range(self.k0, K + 1):
            for a in self.legs:
                out[(a, k)] = self.coefficient(a, k, sigma=sigma, t=t) * z
        return out

    def mass(self, sigma: float) -> float:
        q = self.q_branch(sigma)
        return self.energy * (q ** self.k0) / (1.0 - q)

    def finite_mass(self, sigma: float, K: int) -> float:
        if K < self.k0:
            return 0.0
        q = self.q_branch(sigma)
        n_terms = K - self.k0 + 1
        return self.energy * (q ** self.k0) * (1.0 - q ** n_terms) / (1.0 - q)

    def tail_mass(self, sigma: float, K: int) -> float:
        q = self.q_branch(sigma)
        if K < self.k0:
            return self.mass(sigma)
        return self.energy * (q ** (K + 1)) / (1.0 - q)

    def defect(self, sigma: float) -> float:
        return self.mass(sigma) - 1.0

    def critical_sigma(self, tol: float = 1e-14, max_iter: int = 200) -> float:
        """
        Resolve mass(sigma)=1 por busca binaria.

        Existe solucao unica para energy > 0 porque a massa decresce de infinito para 0.
        """
        if self.energy <= 0.0:
            raise ValueError("energia precisa ser positiva")
        lo = 1e-15
        hi = 1.0
        while self.mass(hi) > 1.0:
            hi *= 2.0
            if hi > 1e6:
                raise RuntimeError("falha ao achar limite superior para critical_sigma")
        for _ in range(max_iter):
            mid = 0.5 * (lo + hi)
            if self.mass(mid) > 1.0:
                lo = mid
            else:
                hi = mid
            if abs(hi - lo) <= tol:
                break
        return 0.5 * (lo + hi)


@dataclass(frozen=True)
class CpTiltOperator:
    """
    Tilt transversal Cp.

    delta = sigma - 1/2

    Theta^{(p)}_delta(c)
      = sum_{a in A_p} (c+a)^(-delta) - |A_p| c^(-delta)

    Para centros Cp canonicos c=p^k m com (m,p)=1.
    """

    p: int
    k_start: int | None = None

    def __post_init__(self) -> None:
        if not is_prime(self.p):
            raise ValueError(f"p precisa ser primo; recebido p={self.p}")
        if self.k_start is not None and self.k_start < 1:
            raise ValueError("k_start precisa ser >= 1")

    @property
    def k0(self) -> int:
        return cp_k0(self.p, self.k_start)

    @property
    def legs(self) -> tuple[int, ...]:
        return cp_legs(self.p)

    @property
    def branch_count(self) -> int:
        return len(self.legs)

    def center(self, k: int, m: int) -> int:
        """Centro c=p^k m, com validacao basica."""
        if k < self.k0:
            raise ValueError(f"k={k} abaixo de k0={self.k0}")
        if m < 1:
            raise ValueError("m precisa ser positivo")
        if math.gcd(m, self.p) != 1:
            raise ValueError(f"m={m} precisa ser coprimo a p={self.p}")
        return (self.p ** k) * m

    def delta_from_sigma(self, sigma: float) -> float:
        if sigma <= 0.0:
            raise ValueError("sigma precisa ser > 0")
        return sigma - 0.5

    def leg_terms(self, c: int, delta: float) -> dict[int, float]:
        """
        Termos por perna:

            a -> (c+a)^(-delta) - c^(-delta)
        """
        if c <= max(abs(a) for a in self.legs):
            raise ValueError(f"centro c={c} pequeno demais para A_p={self.legs}")
        center_value = positive_pow(float(c), -delta)
        return {a: positive_pow(float(c + a), -delta) - center_value for a in self.legs}

    def theta_delta(self, c: int, delta: float) -> float:
        """Theta_delta^{(p)}(c)."""
        return sum(self.leg_terms(c, delta).values())

    def theta_sigma(self, c: int, sigma: float) -> float:
        """Theta_{sigma-1/2}^{(p)}(c)."""
        return self.theta_delta(c, self.delta_from_sigma(sigma))

    def theta_at_address(self, k: int, m: int, sigma: float) -> float:
        """Tilt no centro c=p^k m."""
        return self.theta_sigma(self.center(k, m), sigma)

    def normalized_theta_at_address(self, k: int, m: int, sigma: float) -> float:
        """
        Tilt normalizado por c^(-delta), util para comparar centros.

            Theta(c) / c^(-delta)
        """
        c = self.center(k, m)
        delta = self.delta_from_sigma(sigma)
        denom = positive_pow(float(c), -delta)
        return self.theta_delta(c, delta) / denom

    def regime(self, sigma: float, tol: float = 1e-14) -> str:
        delta = self.delta_from_sigma(sigma)
        if abs(delta) <= tol:
            return "aniquilado"
        if delta > 0:
            return "convexo_pos"
        return "concavo_neg"


def print_branch_report(primes: Iterable[int], sigmas: Iterable[float], K: int) -> None:
    header = (
        f"{'p':>3} {'A_p':>5} {'k0':>3} {'sigma':>9} "
        f"{'mass':>18} {'norm':>14} {'defect':>14} "
        f"{'finite_K':>18} {'tail_K':>14} {'regime':>10}"
    )
    print("\nBranch mass Cp")
    print(header)
    print('-' * len(header))

    for p in primes:
        op = CpBranchOperator(p)
        for sigma in sigmas:
            mass = op.mass(sigma)
            finite = op.finite_mass(sigma, K)
            tail = op.tail_mass(sigma, K)
            print(
                f"{p:3d} {op.branch_count:5d} {op.k0:3d} {sigma:9.5f} "
                f"{mass:18.12g} {op.norm(sigma):14.8g} {op.defect(sigma):14.6g} "
                f"{finite:18.12g} {tail:14.6g} {op.regime(sigma):>10}"
            )


def print_tilt_report(primes: Iterable[int], sigmas: Iterable[float], k: int | None, m: int) -> None:
    header = (
        f"{'p':>3} {'A_p':>5} {'k':>3} {'m':>5} {'c':>12} {'sigma':>9} "
        f"{'delta':>11} {'theta':>18} {'theta_norm':>18} {'regime':>13}"
    )
    print("\nTilt Cp")
    print(header)
    print('-' * len(header))

    for p in primes:
        op = CpTiltOperator(p)
        kk = op.k0 if k is None else k
        if kk < op.k0:
            kk = op.k0
        # Se o m escolhido nao for coprimo a p, corrige para o proximo coprimo.
        mm = m
        while math.gcd(mm, p) != 1:
            mm += 1
        c = op.center(kk, mm)
        for sigma in sigmas:
            delta = op.delta_from_sigma(sigma)
            theta = op.theta_delta(c, delta)
            theta_norm = op.normalized_theta_at_address(kk, mm, sigma)
            print(
                f"{p:3d} {op.branch_count:5d} {kk:3d} {mm:5d} {c:12d} {sigma:9.5f} "
                f"{delta:11.5g} {theta:18.12g} {theta_norm:18.12g} {op.regime(sigma):>13}"
            )


def print_weighted_report(
    p: int,
    sigma: float,
    K: int,
    coeff_text: str,
    normalize: bool,
) -> None:
    legs = cp_legs(p)
    coeffs = parse_leg_coefficients(coeff_text, legs)
    op = CpWeightedBranchOperator(p=p, coefficients=coeffs)
    if normalize:
        op = op.normalized()

    print("\nWeighted branch Cp")
    print(f"p={p}, A_p={legs}, k0={op.k0}")
    print(f"coefficients={{{', '.join(f'{a}: {fmt_complex(op.coefficients.get(a, 0j))}' for a in legs)}}}")
    print(f"energy=sum |alpha_a|^2 = {op.energy:.16g}")
    print(f"critical_energy          = {op.critical_energy:.16g}")
    print(f"critical_sigma           = {op.critical_sigma():.16g}")
    print(f"mass(sigma={sigma})      = {op.mass(sigma):.16g}")
    print(f"defect                   = {op.defect(sigma):.16g}")
    print(f"finite_mass(K={K})       = {op.finite_mass(sigma, K):.16g}")
    print(f"tail_mass(K={K})         = {op.tail_mass(sigma, K):.16g}")
    print(f"tail_identity_error      = {abs(op.finite_mass(sigma, K) + op.tail_mass(sigma, K) - op.mass(sigma)):.3e}")


def print_vector_sample(
    p: int,
    sigma: float,
    t: float,
    K: int,
    z: complex,
    limit: int,
    coeff_text: str | None = None,
    normalize: bool = False,
) -> None:
    """Mostra algumas coordenadas do operador truncado."""
    if coeff_text is None:
        op = CpBranchOperator(p)
        values = op.apply_finite(z=z, sigma=sigma, t=t, K=K)
        legs = op.legs
        title = "W_{p,s} z"
        extra = ""
    else:
        legs = cp_legs(p)
        coeffs = parse_leg_coefficients(coeff_text, legs)
        wop = CpWeightedBranchOperator(p=p, coefficients=coeffs)
        if normalize:
            wop = wop.normalized()
        values = wop.apply_finite(z=z, sigma=sigma, t=t, K=K)
        title = "W_{p,s,alpha} z"
        extra = f", energy={wop.energy:.12g}, critical_sigma={wop.critical_sigma():.12g}"

    print(f"\nAmostra de {title} para p={p}, sigma={sigma}, t={t}, K={K}, z={z}{extra}")
    print(f"A_p={legs}")
    print(f"{'a':>4} {'k':>4} {'valor':>34} {'abs':>14}")
    print('-' * 62)

    for i, ((a, k), value) in enumerate(values.items()):
        if i >= limit:
            remaining = len(values) - limit
            if remaining > 0:
                print(f"... mais {remaining} coordenadas")
            break
        print(f"{a:4d} {k:4d} {fmt_complex(value)} {abs(value):14.6g}")


def print_tilt_terms(p: int, sigma: float, k: int | None, m: int) -> None:
    op = CpTiltOperator(p)
    kk = op.k0 if k is None else max(k, op.k0)
    mm = m
    while math.gcd(mm, p) != 1:
        mm += 1
    c = op.center(kk, mm)
    delta = op.delta_from_sigma(sigma)
    terms = op.leg_terms(c, delta)

    print(f"\nTermos do tilt Cp: p={p}, sigma={sigma}, delta={delta}, k={kk}, m={mm}, c={c}")
    print(f"A_p={op.legs}")
    print(f"{'a':>4} {'term=(c+a)^(-delta)-c^(-delta)':>38}")
    print('-' * 46)
    for a, value in terms.items():
        print(f"{a:4d} {value:38.16e}")
    print(f"theta = {sum(terms.values()):.16e}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Cp Branch + Tilt Operator: massa quadratica, coeficientes por ramo e tilt transversal."
    )
    parser.add_argument(
        "--mode",
        choices=["all", "branch", "tilt", "weighted", "vector", "tilt-terms"],
        default="all",
        help="Modo de execucao.",
    )
    parser.add_argument("--primes", default="2,3,5,7,11", help="Lista de primos, ex: 2,3,5,7")
    parser.add_argument("--sigmas", default="0.25,0.5,1.0", help="Lista de sigmas, ex: 0.25,0.5,1.0")
    parser.add_argument("--K", type=int, default=6, help="Profundidade final para truncamento")
    parser.add_argument("--p", type=int, default=5, help="Primo para modos locais")
    parser.add_argument("--sigma", type=float, default=0.5, help="Sigma para modos locais")
    parser.add_argument("--t", type=float, default=14.134725, help="Altura t da amostra vetorial")
    parser.add_argument("--z", default="1+0j", help="Entrada complexa z, ex: 1+0j ou 2-3i")
    parser.add_argument("--limit", type=int, default=24, help="Quantidade de coordenadas na amostra vetorial")
    parser.add_argument("--k", type=int, default=0, help="Profundidade para tilt. 0=usar k0 canonico")
    parser.add_argument("--m", type=int, default=1, help="Nucleo horizontal para tilt")
    parser.add_argument(
        "--coeffs",
        default="uniform",
        help="Coeficientes por perna, ex: 'uniform' ou '-2:1,-1:i,1:-i,2:1'",
    )
    parser.add_argument(
        "--normalize-coeffs",
        action="store_true",
        help="Normaliza coeficientes para mass(1/2)=1.",
    )

    args = parser.parse_args()
    primes = parse_int_list(args.primes)
    sigmas = parse_float_list(args.sigmas)
    k_for_tilt = None if args.k == 0 else args.k

    print("Cp Branch + Tilt Operator")
    print("=========================")

    if args.mode in {"all", "branch"}:
        print_branch_report(primes=primes, sigmas=sigmas, K=args.K)

        print("\nTeste da linha critica sigma=1/2")
        for p in primes:
            op = CpBranchOperator(p)
            print(
                f"p={p:2d}: mass(1/2)={op.mass(0.5):.16f}, "
                f"tail_identity_error(K={args.K})={op.check_tail_identity(0.5, args.K):.3e}"
            )

    if args.mode in {"all", "tilt"}:
        print_tilt_report(primes=primes, sigmas=sigmas, k=k_for_tilt, m=args.m)

    if args.mode in {"all", "weighted"}:
        print_weighted_report(
            p=args.p,
            sigma=args.sigma,
            K=args.K,
            coeff_text=args.coeffs,
            normalize=args.normalize_coeffs,
        )

    if args.mode == "vector":
        print_vector_sample(
            p=args.p,
            sigma=args.sigma,
            t=args.t,
            K=args.K,
            z=parse_complex(args.z),
            limit=args.limit,
            coeff_text=args.coeffs,
            normalize=args.normalize_coeffs,
        )

    if args.mode == "tilt-terms":
        print_tilt_terms(p=args.p, sigma=args.sigma, k=k_for_tilt, m=args.m)


if __name__ == "__main__":
    main()
