import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import CirclePacking.RootIsolation

namespace CirclePacking

/-!
# The known seven-circle Henneberg branch

This file records the actual real-valued closure residual used by the
numerical audit.  It intentionally separates the definition of the residual
from the later interval proof of continuity and monotonicity.
-/

structure Point where
  x : ℝ
  y : ℝ

namespace Point

def sub (p q : Point) : Point := ⟨p.x - q.x, p.y - q.y⟩

def add (p q : Point) : Point := ⟨p.x + q.x, p.y + q.y⟩

def smul (a : ℝ) (p : Point) : Point := ⟨a * p.x, a * p.y⟩

def dot (p q : Point) : ℝ := p.x * q.x + p.y * q.y

def normSq (p : Point) : ℝ := p.dot p

def perp (p : Point) : Point := ⟨-p.y, p.x⟩

end Point

open Point

def radius (i : ℕ) : ℝ := Real.sqrt i

def origin : Point := ⟨0, 0⟩

/- The sign parameter is represented by `σ = 1` or `σ = -1`; the formula is
   total as a real function, while its geometric interpretation is used only
   on the certified nondegenerate interval. -/
def circleIntersection (a b : Point) (da db σ : ℝ) : Point :=
  let dvec := b.sub a
  let d2 := dvec.normSq
  let d := Real.sqrt d2
  let t := (da ^ 2 - db ^ 2 + d ^ 2) / (2 * d)
  let h2 := da ^ 2 - t ^ 2
  let h := Real.sqrt h2
  let e := dvec.smul (1 / d)
  let base := a.add (e.smul t)
  base.add ((e.perp).smul (σ * h))

def p5 (R : ℝ) : Point := ⟨R - radius 5, 0⟩

def p7 (R : ℝ) : Point :=
  circleIntersection origin (p5 R) (R - radius 7) (radius 5 + radius 7) 1

def p10 (R : ℝ) : Point :=
  circleIntersection (p5 R) (p7 R) (radius 5 + radius 10)
    (radius 7 + radius 10) 1

def p6 (R : ℝ) : Point :=
  circleIntersection origin (p10 R) (R - radius 6)
    (radius 6 + radius 10) (-1)

def p8 (R : ℝ) : Point :=
  circleIntersection origin (p6 R) (R - radius 8)
    (radius 6 + radius 8) (-1)

def p9 (R : ℝ) : Point :=
  circleIntersection origin (p7 R) (R - radius 9)
    (radius 7 + radius 9) 1

def p2 (R : ℝ) : Point :=
  circleIntersection origin (p9 R) (R - radius 2)
    (radius 2 + radius 9) 1

def hennenbergClosureResidual (R : ℝ) : ℝ :=
  (p2 R).sub (p8 R) |>.normSq - (radius 2 + radius 8) ^ 2

/- `R0` is intentionally parameterized by its certified root-isolation
   certificate.  This prevents a rounded decimal from silently becoming the
   mathematical definition of the claimed radius. -/
noncomputable def R0
    (cert : RootIsolationCertificate hennenbergClosureResidual) : ℝ :=
  cert.root

theorem R0_spec
    (cert : RootIsolationCertificate hennenbergClosureResidual) :
    R0 cert ∈ Set.Icc cert.lo cert.hi ∧
      hennenbergClosureResidual (R0 cert) = 0 := by
  exact cert.root_spec

end CirclePacking
