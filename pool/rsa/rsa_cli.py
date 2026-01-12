#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
rsa_cli.py

RSAを「暗号(encrypt/decrypt)」と「署名(sign/verify)」として明示的に扱うCLI。

- encrypt : 公開鍵 (n,e) で m^e mod n
- decrypt : 秘密鍵 (p,q,e から導出した d) で c^d mod n
- sign    : 秘密鍵 (d) で m^d mod n
- verify  : 公開鍵 (n,e) で s^e mod n

入力：
- encrypt/sign  : ASCII文字列（スペースを含む場合もOK）
- decrypt/verify: 数値列（空白区切り or カンマ区切り、桁区切りカンマもOK）

鍵指定：
- --key/-k "p,q,e"   : 秘密鍵(素数p,q)＋公開指数e。nとdを内部で計算。
- --key/-k "n"       : 公開鍵の法nのみ（eは --e-default を使用）
- --key/-k "n,e"     : 公開鍵の法nと指数e

追加ユーティリティ：
- --private-key/-v "a,b,e" : a,b,e から n=a*b を10進で出力
- --public-key/-b  "n"     : n を素因数分解して a,b を出力（eは推定できないので --e-default を併記）
- --gen/-g "n_digits,e"    : n が n_digits 桁になるように a,b をランダム生成して表示（sympy必須）
"""

import argparse
import secrets
from dataclasses import dataclass
from math import gcd
from typing import List, Optional, Tuple


# ---------- number theory helpers ----------

def egcd(a: int, b: int) -> Tuple[int, int, int]:
    if b == 0:
        return a, 1, 0
    g, x1, y1 = egcd(b, a % b)
    return g, y1, x1 - (a // b) * y1


def modinv(a: int, m: int) -> int:
    g, x, _ = egcd(a, m)
    if g != 1:
        raise ValueError(f"modinv: gcd({a},{m})={g} != 1")
    return x % m


def parse_int(s: str) -> int:
    # 10進数のみ。桁区切りのカンマ/アンダースコアを許可。
    return int(s.replace(",", "").replace("_", "").strip())


def parse_numbers(argv_items: List[str]) -> List[int]:
    """
    数値入力を許容：
      - 空白区切り: 12 34 56
      - カンマ区切り: "12,34,56"
      - 混在: "12,34"  "56"
    ※ただし「桁区切りカンマ」と「区切りカンマ」は両方あり得るので、
      - トークン全体が整数になればそれを優先（例: "5,960,061,347" は1個の整数）
      - 整数にならなければ区切りとして分割
    """
    nums: List[int] = []
    for item in argv_items:
        item = item.strip()
        if not item:
            continue

        # まず「桁区切り込み整数」として解釈できるなら、それを採用
        try:
            nums.append(parse_int(item))
            continue
        except Exception:
            pass

        # だめなら区切りカンマとして分割
        compact = item.replace(" ", "")
        parts = [p for p in compact.split(",") if p != ""]
        for p in parts:
            nums.append(parse_int(p))
    return nums


def looks_like_numbers(argv_items: List[str]) -> bool:
    if not argv_items:
        return False
    try:
        _ = parse_numbers(argv_items)
        return True
    except Exception:
        return False


# ---------- RSA core ----------

@dataclass(frozen=True)
class RSAKey:
    n: int
    e: int
    d: Optional[int] = None  # private exponent


def parse_key(key_str: str, default_e: int) -> Tuple[RSAKey, str]:
    """
    --key/-k supports:
      1) "p,q,e"  -> compute n and d
      2) "n"      -> public only, uses default_e
      3) "n,e"    -> public only
    Returns (RSAKey, key_kind) where key_kind in {"private","public"}.
    """
    parts = [p.strip() for p in key_str.split(",") if p.strip() != ""]
    if len(parts) == 1:
        n = parse_int(parts[0])
        return RSAKey(n=n, e=default_e, d=None), "public"
    if len(parts) == 2:
        n = parse_int(parts[0])
        e = parse_int(parts[1])
        return RSAKey(n=n, e=e, d=None), "public"
    if len(parts) == 3:
        p = parse_int(parts[0])
        q = parse_int(parts[1])
        e = parse_int(parts[2])
        n = p * q
        phi = (p - 1) * (q - 1)
        if gcd(e, phi) != 1:
            raise ValueError(
                f"e must be coprime to phi=(p-1)(q-1)={phi}; gcd(e,phi)={gcd(e,phi)}")
        d = modinv(e, phi)
        return RSAKey(n=n, e=e, d=d), "private"
    raise ValueError("--key must be one of: 'p,q,e' or 'n' or 'n,e'")


def rsa_pow(values: List[int], exp: int, n: int) -> List[int]:
    return [pow(v, exp, n) for v in values]


# ---------- factoring / prime generation (needs sympy) ----------

def _require_sympy():
    try:
        import sympy as sp  # type: ignore
        return sp
    except Exception as ex:
        raise RuntimeError(
            "This feature requires sympy. Install: pip install sympy") from ex


def factor_semiprime(n: int) -> Tuple[int, int]:
    sp = _require_sympy()
    fac = sp.factorint(n)  # dict prime->exp
    primes: List[int] = []
    for p, k in fac.items():
        primes.extend([int(p)] * int(k))
    if len(primes) != 2:
        raise ValueError(
            f"Expected n to be product of exactly 2 primes, got: {fac}")
    a, b = sorted(primes)
    return a, b


def random_prime_with_digits(digits: int) -> int:
    sp = _require_sympy()
    if digits < 1:
        raise ValueError("digits must be >= 1")
    lo = 10 ** (digits - 1)
    hi = 10 ** digits - 1
    while True:
        x = secrets.randbelow(hi - lo + 1) + lo
        if x % 2 == 0:
            x += 1
        p = int(sp.nextprime(x))
        if lo <= p <= hi:
            return p


def gen_rsa_keypair_by_ndigits(n_digits: int, e: int) -> Tuple[int, int, int, int, int]:
    """
    Generate (a,b,n,e,d) such that n=a*b has exactly n_digits decimal digits,
    and gcd(e, (a-1)(b-1))=1.
    """
    if n_digits < 2:
        raise ValueError("n_digits must be >= 2")

    da = max(1, n_digits // 2)
    db = max(1, n_digits - da)

    target_lo = 10 ** (n_digits - 1)
    target_hi = 10 ** n_digits - 1

    while True:
        a = random_prime_with_digits(da)
        b = random_prime_with_digits(db)
        if a == b:
            continue
        n = a * b
        if not (target_lo <= n <= target_hi):
            continue
        phi = (a - 1) * (b - 1)
        if gcd(e, phi) != 1:
            continue
        d = modinv(e, phi)
        a, b = sorted((a, b))
        return a, b, n, e, d


# ---------- I/O helpers ----------

def ascii_to_ints(s: str) -> List[int]:
    return list(s.encode("ascii", errors="strict"))


def ints_to_ascii(vals: List[int]) -> Optional[str]:
    if not all(0 <= v <= 255 for v in vals):
        return None
    try:
        return bytes(vals).decode("ascii")
    except Exception:
        return None


# ---------- modes ----------

MODE_ENCRYPT = "encrypt"
MODE_DECRYPT = "decrypt"
MODE_SIGN = "sign"
MODE_VERIFY = "verify"
ALL_MODES = [MODE_ENCRYPT, MODE_DECRYPT, MODE_SIGN, MODE_VERIFY]


def do_encrypt(key: RSAKey, text: str) -> str:
    m = ascii_to_ints(text)
    c = rsa_pow(m, key.e, key.n)
    return ",".join(str(x) for x in c)


def do_decrypt(key: RSAKey, nums: List[int]) -> str:
    if key.d is None:
        raise ValueError("decrypt requires private key (p,q,e) to compute d.")
    m = rsa_pow(nums, key.d, key.n)
    s = ints_to_ascii(m)
    return s if s is not None else ",".join(str(x) for x in m)


def do_sign(key: RSAKey, text: str) -> str:
    if key.d is None:
        raise ValueError("sign requires private key (p,q,e) to compute d.")
    m = ascii_to_ints(text)
    s = rsa_pow(m, key.d, key.n)
    return ",".join(str(x) for x in s)


def do_verify(key: RSAKey, nums: List[int]) -> str:
    m = rsa_pow(nums, key.e, key.n)
    s = ints_to_ascii(m)
    return s if s is not None else ",".join(str(x) for x in m)


# ---------- key utility actions ----------

def action_private_key(triple: str) -> None:
    parts = [p.strip() for p in triple.split(",") if p.strip() != ""]
    if len(parts) != 3:
        raise ValueError("--private-key expects 'a,b,e'")
    a = parse_int(parts[0])
    b = parse_int(parts[1])
    # eは受け取るが、ここでは公開鍵(n)を出す用途なのでnだけ出力
    _ = parse_int(parts[2])
    print(a * b)


def action_public_key(n_str: str, e_default: int) -> None:
    n = parse_int(n_str)
    a, b = factor_semiprime(n)
    print(f"a={a}")
    print(f"b={b}")
    print(f"n={n}")
    print(
        f"e={e_default}  # NOTE: e cannot be derived from n alone; this is --e-default")


def action_gen(spec: str) -> None:
    parts = [p.strip() for p in spec.split(",") if p.strip() != ""]
    if len(parts) != 2:
        raise ValueError("--gen expects 'n_digits,e'")
    n_digits = int(parts[0])
    e = parse_int(parts[1])
    a, b, n, e, d = gen_rsa_keypair_by_ndigits(n_digits, e)

    print(f"a={a}")
    print(f"b={b}")
    print(f"n={n}")
    print(f"e={e}")
    print(f"d={d}")
    print(f"private_key(p,q,e)={a},{b},{e}")
    print(f"public_key(n,e)={n},{e}")


# ---------- CLI ----------

def main() -> None:
    ap = argparse.ArgumentParser(
        description="RSA CLI with explicit modes: encrypt/decrypt + sign/verify."
    )

    ap.add_argument("--e-default", type=int, default=65537,
                    help="Default public exponent when key is 'n' only. (default: 65537)")

    # key utilities
    ap.add_argument("-v", "--private-key", metavar="a,b,e",
                    help="Given a,b,e compute and print public modulus n=a*b (decimal).")
    ap.add_argument("-b", "--public-key", metavar="n",
                    help="Given public modulus n, factor to a,b and print them (requires sympy).")
    ap.add_argument("-g", "--gen", metavar="n_digits,e",
                    help="Generate random keypair so that n has n_digits decimal digits (requires sympy).")

    # main crypto options
    ap.add_argument("-k", "--key",
                    help=("Key formats: 'p,q,e' (private primes + e) OR 'n' OR 'n,e'. "
                          "Use mode encrypt/verify with public key; decrypt/sign require private key."))
    ap.add_argument("-m", "--mode", choices=ALL_MODES,
                    help=("Mode: encrypt/decrypt/sign/verify. "
                          "If omitted, auto: numbers->decrypt, otherwise->encrypt."))

    ap.add_argument("data", nargs="*",
                    help="Text (for encrypt/sign) OR numbers (for decrypt/verify).")

    args = ap.parse_args()

    # Utility actions take priority
    if args.private_key:
        action_private_key(args.private_key)
        return
    if args.public_key:
        action_public_key(args.public_key, args.e_default)
        return
    if args.gen:
        action_gen(args.gen)
        return

    if not args.key:
        ap.error("Missing --key/-k (unless using --private-key/--public-key/--gen).")
    if not args.data:
        ap.error("Missing input data.")

    key, key_kind = parse_key(args.key, args.e_default)

    # Auto mode if not provided
    mode = args.mode
    if mode is None:
        mode = MODE_DECRYPT if looks_like_numbers(args.data) else MODE_ENCRYPT

    if mode in (MODE_ENCRYPT, MODE_SIGN):
        text = " ".join(args.data)
        if mode == MODE_ENCRYPT:
            # public key OK
            print(do_encrypt(key, text))
        else:
            # sign requires private exponent d
            if key_kind != "private" or key.d is None:
                raise SystemExit(
                    "ERROR: sign requires private key in format 'p,q,e'.")
            print(do_sign(key, text))
        return

    # decrypt/verify expect numbers
    nums = parse_numbers(args.data)
    if mode == MODE_DECRYPT:
        if key_kind != "private" or key.d is None:
            raise SystemExit(
                "ERROR: decrypt requires private key in format 'p,q,e'.")
        print(do_decrypt(key, nums))
    else:
        # verify uses public exponent e
        print(do_verify(key, nums))


if __name__ == "__main__":
    main()


"""
USAGE EXAMPLES

(1) 暗号（公開鍵で暗号化、秘密鍵で復号）
  # encrypt with public key (n only, e defaults to 65537)
  python rsa_cli.py -k 5960061347 encryptme
  # decrypt with private key (p,q,e)
  python rsa_cli.py -k 75821,78607,65537 5182981400 65567356 ...

(2) 署名（秘密鍵で署名、公開鍵で検証）
  # sign with private key
  python rsa_cli.py -m sign -k 75821,78607,65537 ikura
  # verify with public key
  python rsa_cli.py -m verify -k 5960061347 <signature numbers...>

(3) 公開鍵nを出す
  python rsa_cli.py -v 75821,78607,65537

(4) 公開鍵nを素因数分解（sympy必要）
  python rsa_cli.py -b 5960061347

(5) nが20桁になる鍵生成（sympy必要）
  python rsa_cli.py -g 20,65537
"""
