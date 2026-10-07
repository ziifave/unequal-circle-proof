"""Published best-known n=10 configuration, normalized to its container."""
from __future__ import annotations

from decimal import Decimal

# Source: Packomania CCIR n=10 coordinate file, retrieved 2026-10-05.
# Its outer radius is one and r_1=1/R.  Scaling these centres by R0 therefore
# gives the target convention r_i=sqrt(i), outer radius R0.
R0 = Decimal("8.3034681221114890787043811875")
NORMALIZED_CENTRES: tuple[tuple[Decimal, Decimal], ...] = (
    (Decimal("0.479246929133513701481040234253"), Decimal("0.737140714086066530228751600274")),
    (Decimal("0.800027722290656233860906387785"), Decimal("-0.219843504108248706355541213948")),
    (Decimal("-0.781765846908040447247657177314"), Decimal("0.093163698290269002090735401602")),
    (Decimal("-0.673500270351836582863984382324"), Decimal("-0.346108891919538295855870735014")),
    (Decimal("-0.520657363843163739304068691648"), Decimal("0.512687286073517748242011029666")),
    (Decimal("-0.227047522039187591044874589162"), Decimal("-0.667442946189220861622581159935")),
    (Decimal("0.042954592969046536282740458994"), Decimal("0.680012607709664173743601302042")),
    (Decimal("0.393361033710743020739985580955"), Decimal("-0.529181660079646647504553447105")),
    (Decimal("0.581283062358446278266302817319"), Decimal("0.264677750360810769549858525289")),
    (Decimal("-0.120879140055017061305321685827"), Decimal("0")),
)


def centres_in_target_convention() -> tuple[tuple[Decimal, Decimal], ...]:
    # x -> -x, y -> -y establishes the solver's rotation/reflection convention:
    # c_10 lies on +x and c_9 has y >= 0.
    return tuple((-R0 * x, -R0 * y) for x, y in NORMALIZED_CENTRES)
