from pathlib import Path
from typing import Callable, Optional
import csv
import importlib.util

_BIP340_REFERENCE = Path(__file__).resolve().parents[1] / "bip-0340" / "reference.py"
_spec = importlib.util.spec_from_file_location("bip340_reference", _BIP340_REFERENCE)
assert _spec is not None and _spec.loader is not None
_bip340 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_bip340)

G = _bip340.G
Point = _bip340.Point
bytes_from_int = _bip340.bytes_from_int
bytes_from_point = _bip340.bytes_from_point
has_even_y = _bip340.has_even_y
int_from_bytes = _bip340.int_from_bytes
is_infinite = _bip340.is_infinite
lift_x = _bip340.lift_x
n = _bip340.n
p = _bip340.p
point_add = _bip340.point_add
point_mul = _bip340.point_mul
tagged_hash = _bip340.tagged_hash
xor_bytes = _bip340.xor_bytes
y = _bip340.y

VerifyOpening = Callable[[bytes, Point, bytes], bool]


def cbytes(P: Point) -> bytes:
    return bytes([2 if has_even_y(P) else 3]) + bytes_from_point(P)


def point_neg(P: Point) -> Point:
    return (P[0], (-y(P)) % p)


def pubpoint_gen(seckey: bytes) -> Point:
    d = int_from_bytes(seckey)
    if not (1 <= d <= n - 1):
        raise ValueError("The secret key must be an integer in the range 1..n-1.")
    P = point_mul(G, d)
    assert P is not None
    return P


def recoverable_sign(
    msg: bytes,
    seckey: bytes,
    q: bytes,
    opening: bytes,
    aux_rand: bytes,
    verify_opening: VerifyOpening,
) -> bytes:
    if len(q) != 32:
        raise ValueError("q must be 32 bytes.")
    if len(aux_rand) != 32:
        raise ValueError("aux_rand must be 32 bytes.")
    d = int_from_bytes(seckey)
    if not (1 <= d <= n - 1):
        raise ValueError("The secret key must be an integer in the range 1..n-1.")
    P = point_mul(G, d)
    assert P is not None
    if not verify_opening(q, P, opening):
        raise ValueError("The opening does not commit to the public key.")

    h = tagged_hash("RecSchnorr/opening", opening)
    t = xor_bytes(bytes_from_int(d), tagged_hash("RecSchnorr/aux", aux_rand))
    rand = tagged_hash("RecSchnorr/nonce", t + cbytes(P) + q + h + msg)
    k0 = int_from_bytes(rand) % n
    if k0 == 0:
        raise RuntimeError("Failure. This happens only with negligible probability.")
    R0 = point_mul(G, k0)
    assert R0 is not None
    k = k0 if has_even_y(R0) else n - k0
    R = point_mul(G, k)
    assert R is not None
    e = int_from_bytes(tagged_hash("RecSchnorr/challenge", bytes_from_point(R) + q + h + msg)) % n
    if e == 0:
        raise RuntimeError("Failure. This happens only with negligible probability.")
    s = (k + e * d) % n
    if point_mul(G, s) != point_add(point_mul(G, k), point_mul(P, e)):
        raise RuntimeError("The created signature does not satisfy the signing equation.")
    sig = bytes_from_point(R) + bytes_from_int(s)
    return sig


def recoverable_verify(
    msg: bytes,
    q: bytes,
    opening: bytes,
    sig: bytes,
    verify_opening: VerifyOpening,
) -> Optional[Point]:
    if len(q) != 32:
        raise ValueError("q must be 32 bytes.")
    if len(sig) != 64:
        raise ValueError("The signature must be a 64-byte array.")

    h = tagged_hash("RecSchnorr/opening", opening)
    r = int_from_bytes(sig[0:32])
    s = int_from_bytes(sig[32:64])
    if r >= p or s >= n:
        return None
    R = lift_x(r)
    if R is None:
        return None
    e = int_from_bytes(tagged_hash("RecSchnorr/challenge", bytes_from_point(R) + q + h + msg)) % n
    if e == 0:
        return None
    S = point_add(point_mul(G, s), point_neg(R))
    P = point_mul(S, pow(e, n - 2, n))
    if P is None or is_infinite(P):
        return None
    if not verify_opening(q, P, opening):
        return None
    return P


# These toy opening relations are only for test vectors. Applications must
# define their own VerifyOpening relation and analyze opening soundness,
# fixed-opening binding, canonical opening serialization, and collision
# resistance of the opening hash.
def compressed_commitment(P: Point, opening: bytes = b"") -> bytes:
    if opening != b"":
        raise ValueError("compressed commitment uses an empty opening.")
    return tagged_hash("RecSchnorrTest/compressed", cbytes(P))


def verify_compressed_opening(q: bytes, P: Point, opening: bytes) -> bool:
    return opening == b"" and q == compressed_commitment(P, opening)


def opening_commitment(P: Point, opening: bytes) -> bytes:
    return tagged_hash("RecSchnorrTest/opening", cbytes(P) + opening)


def verify_opening_commitment(q: bytes, P: Point, opening: bytes) -> bool:
    return q == opening_commitment(P, opening)


VERIFY_OPENING = {
    "compressed": verify_compressed_opening,
    "opening": verify_opening_commitment,
}


def test_vectors() -> bool:
    all_passed = True
    path = Path(__file__).resolve().parent / "test-vectors.csv"
    with path.open(newline="") as csvfile:
        reader = csv.reader(csvfile)
        next(reader)
        for row in reader:
            (
                index,
                scheme,
                seckey_hex,
                pubkey_hex,
                q_hex,
                opening_hex,
                aux_rand_hex,
                msg_hex,
                sig_hex,
                result_str,
                comment,
            ) = row
            verify_opening = VERIFY_OPENING[scheme]
            q = bytes.fromhex(q_hex)
            opening = bytes.fromhex(opening_hex)
            msg = bytes.fromhex(msg_hex)
            sig = bytes.fromhex(sig_hex)
            result = result_str == "TRUE"
            print("\nTest vector", ("#" + index).rjust(3, " ") + ":")

            if seckey_hex != "":
                seckey = bytes.fromhex(seckey_hex)
                aux_rand = bytes.fromhex(aux_rand_hex)
                P = pubpoint_gen(seckey)
                if pubkey_hex != cbytes(P).hex().upper():
                    print(" * Failed key generation.")
                    all_passed = False
                try:
                    sig_actual = recoverable_sign(msg, seckey, q, opening, aux_rand, verify_opening)
                    if sig == sig_actual:
                        print(" * Passed signing test.")
                    else:
                        print(" * Failed signing test.")
                        print("   Expected signature:", sig.hex().upper())
                        print("     Actual signature:", sig_actual.hex().upper())
                        all_passed = False
                except RuntimeError as e:
                    print(" * Signing test raised exception:", e)
                    all_passed = False

            P_actual = recoverable_verify(msg, q, opening, sig, verify_opening)
            result_actual = P_actual is not None
            if result and P_actual is not None and pubkey_hex != "":
                result_actual = cbytes(P_actual).hex().upper() == pubkey_hex
            if result == result_actual:
                print(" * Passed verification test.")
            else:
                print(" * Failed verification test.")
                print("   Expected verification result:", result)
                print("     Actual verification result:", result_actual)
                if P_actual is not None:
                    print("     Actual recovered key:", cbytes(P_actual).hex().upper())
                print("   Comment:", comment)
                all_passed = False
    return all_passed


if __name__ == "__main__":
    if not test_vectors():
        raise SystemExit(1)
