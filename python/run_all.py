"""Run all thet-logos numerical engines and report a PASS/FAIL summary."""
import sys
import traceback

from thet_logos import tro, order_zero, order_one, spectral_gap, modular_flow, engine_cycle, thermalize, protolingua

ENGINES = [
    ("tro (TRO identities + tripotent census)", tro.main),
    ("order_zero (order-zero + KO relations)", order_zero.main),
    ("order_one (probes + 576-pair census)", order_one.main),
    ("spectral_gap (Thet Engine simulation)", spectral_gap.main),
    ("modular_flow (thermal time)", modular_flow.main),
    ("engine_cycle (thet-engine graduation: Otto on D_F^2)", engine_cycle.main),
    ("thermalize (dynamic density-matrix thermalization: Lindblad -> Gibbs, K(t) clock)", thermalize.main),
    ("protolingua (THET Proto-Lingua Greek: L0 alphabet + Theta sectors + LOGOS cycle)", protolingua.main),
]


def main():
    ok = True
    for name, fn in ENGINES:
        print("=" * 64)
        print(f"ENGINE: {name}")
        try:
            fn()
        except Exception:
            ok = False
            print(f"[{name}] FAILED")
            traceback.print_exc()
    print("=" * 64)
    print("ALL ENGINES PASS" if ok else "SOME ENGINES FAILED")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
