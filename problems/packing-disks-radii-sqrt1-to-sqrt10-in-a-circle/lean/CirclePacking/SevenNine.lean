import CirclePacking.SevenNineAngles

namespace CirclePacking

/- The 46,080 cell masks are generated from the MPFI certificate, but are
   deliberately kept out of the Lean syntax tree. `include_str` embeds the
   text at elaboration time; the parser below is part of the replay. -/
def sevenNineRawMasks : String :=
  include_str "../../certificates/fixed-order-radial-partition7-mpfi-7.9.masks"

def parseMaskLine (line : String) : Option Nat :=
  line.trimAscii.toNat?

def sevenNineMasks : Array Nat :=
  (sevenNineRawMasks.splitOn "\n").filterMap parseMaskLine |>.toArray

def sevenNineCoefficient : Rat := (999999999999 : Rat) / 1000000000000

def pairIndex (i j : Nat) : Nat :=
  i * 7 - i * (i + 1) / 2 + (j - i - 1)

def angleIndex (i j si sj : Nat) : Nat :=
  pairIndex i j * 4 + si * 2 + sj

def angleFor (state i j : Nat) : Rat :=
  let si := (state >>> i) % 2
  let sj := (state >>> j) % 2
  let a := min i j
  let b := max i j
  let sa := if i ≤ j then si else sj
  let sb := if i ≤ j then sj else si
  sevenNineAngleLower[angleIndex a b sa sb]!

/- The second directed path is the complementary path from b to a.  The
   explicit modular definition avoids any dependence on a graph library. -/
def rowUsesGap' (n a b gap : Nat) (forward : Bool) : Bool :=
  let start := if forward then a else b
  let length := if forward then b - a else n - (b - a)
  (List.range length).any (fun t => (start + t) % n == gap)

def maskBit (mask row : Nat) : Bool :=
  (mask >>> row) % 2 == 1

/- This overload supplies the order-independent path geometry. -/
def cellColumnCountFor (mask : Nat) (gap : Nat) : Nat :=
  (List.range 42).foldl (fun count row =>
    let pairNo := row / 2
    let forward := row % 2 == 0
    let pairs := (List.range 7).flatMap (fun a =>
      (List.range (7 - a - 1)).map (fun k => (a, a + k + 1)))
    let (a, b) := pairs[pairNo]!
    if maskBit mask row && rowUsesGap' 7 a b gap forward then count + 1 else count) 0

def cellColumnOK (mask : Nat) : Bool :=
  (List.range 7).all (fun gap => cellColumnCountFor mask gap ≤ 1)

def cellDualSum (order : Array Nat) (state mask : Nat) : Rat :=
  (List.range 42).foldl (fun total row =>
    if maskBit mask row then
      let pairNo := row / 2
      let pairs := (List.range 7).flatMap (fun a =>
        (List.range (7 - a - 1)).map (fun k => (a, a + k + 1)))
      let (localI, localJ) := pairs[pairNo]!
      let i := order[localI]! - 4
      let j := order[localJ]! - 4
      total + sevenNineCoefficient * angleFor state i j
    else total) 0

def cellOK (index : Nat) : Bool :=
  let order := sevenNineOrders[index / 128]!
  let state := index % 128
  let mask := sevenNineMasks[index]!
  cellColumnOK mask &&
    (2 * ((31416 : Rat) / 10000) < cellDualSum order state mask)

def chunkOK (chunk : Nat) : Bool :=
  (List.range 256).all (fun offset => cellOK (chunk * 256 + offset))

def allChunksOK : Bool :=
  (List.range 180).all chunkOK

/- The finite rational Farkas replay.  The angle values used here are the
   outward-rounded lower bounds supplied by the MPFI certificate.  The
   separate analytic obligation is to certify those 84 bounds from the
   cosine/Taylor inequalities. -/
theorem sevenNine_finite_replay : allChunksOK = true := by
  native_decide

end CirclePacking
