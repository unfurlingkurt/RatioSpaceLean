/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S01.Pres
import RatioSpace.ElementsI.S03.Walk
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
/-!
  **The Unified Kurtonian Biomathematical Theorem Suite, machine-checked.**

  Source: *RatioSpace / Aramis Logic — The Unified Kurtonian Biomathematical
  Theorem Suite v1.0*, Drive, 2026-09-09 05:50.

  The suite's theorems are exact statements in the `(H, R) ∈ ℤ²` nucleotide
  lattice and in `SL(2,ℤ)`. Nothing in it was machine-checked. The ones below
  are finite and decidable, so they are `decide`d here rather than argued.

  **One correction, and it is a wording correction, not a result.** Theorem 2
  states that synonymous mutations at the middle base number zero. Among the
  twenty amino acids that is exactly right and is proved below. Read literally
  it is false: `TAA ↔ TGA` is a middle-base change preserving the reading, but
  both are STOP, not an amino acid. The document should say *amino acid*.

  **The holonomy halves, 2026-09-10 21:30**, Theorems 7, 8, 11 and 14, stated
  with their full quantifier over `Braid.lean`'s `Mat2`. The quantifier says
  what each one depends on; see the section at the end.

  **Theorems 9, 13 and 15, 2026-09-11 00:30.** 9's bracket is antisymmetry and
  its deamination half carries the content; 13 holds exactly, two of eight;
  15 fails as written: its five digits span two depths, Digit III is not
  self-reciprocal, and a mirror-closed hand of odd size must contain `1:1`.

  **Theorem 3, 2026-09-11 02:30.** The 268 contexts are fixed by the code, 67
  synonymous pairs times four next bases. The count is 188, not 180, and the
  split cannot be 46, 80, 54: compound equals stall only, forced by the unit
  square and by Theorem 2, whose middle-base zero is proved here from the same
  table (until now it was a census in Python, not a theorem in this file).

  **Theorem 5, 2026-09-12 02:30.** A two-step barcode is a set of three-base
  words. The donor gate is exactly one of the 64, `GGT`: the `GT` rule plus
  the demand that the exon end in `G`. It therefore rejects nothing — 180
  firings across two never-spliced genomes,
  `research/experiments/splice_barcode_gate.py`. The 3' barcode read as three
  consecutive steps forces `C A | A`, contradicting the `AG` terminus; read
  against the canonical `C A G | G` it drops the step `δ(A,G) = (+1,0)`.
  `ΔR = 0` is ring class, not pyrimidine, so a purine tract and a pyrimidine
  tract are one walk and the polypyrimidine tract is invisible to steps. The
  ligation dwell is derived from the other two.

  **Theorem 10, 2026-09-11 06:30.** The frame identity is re-indexing and holds
  for every sequence (`frame_plus_one`). phiX174's B sits two bases into A's
  frame, not one, so for A and B the identity is `frame_plus_two`: A's boundary
  step is B's first internal step. The suite's is D and E's. The genome half,
  and the 60.7% no reading reproduces, are
  `research/experiments/phix174_overlap_frames.py`.
-/

namespace RatioSpace
namespace Bio

/-- The four canonical bases. `U` is `T`'s coordinate twin and is not a
    separate constructor: the suite gives them the same lattice point. -/
inductive Base where
  | T | C | A | G
deriving DecidableEq, Repr

/-- Hydrogen-bonding capacity, `H ∈ {2,3}`. -/
def H : Base → ℕ
  | .T => 2 | .C => 3 | .A => 2 | .G => 3

/-- Ring volume, `R ∈ {1,2}`: pyrimidines one ring, purines two. -/
def R : Base → ℕ
  | .T => 1 | .C => 1 | .A => 2 | .G => 2

/-- The exact step between two bases, `(ΔH, ΔR) ∈ ℤ²`. -/
def delta (x y : Base) : ℤ × ℤ := ((H y : ℤ) - H x, (R y : ℤ) - R x)

/-- Manhattan step tension `τ(δ) = |ΔH| + |ΔR|`. -/
def tau (x y : Base) : ℤ := |(delta x y).1| + |(delta x y).2|

/-- **Theorem 1 — the constant-width cylinder invariant.**
    Every Watson-Crick pair and the `G:U` wobble pair sums to three rings.
    Note `U = T` in this lattice, so `G:U` is the `G:T` row. -/
theorem constant_width :
    R .A + R .T = 3 ∧ R .G + R .C = 3 ∧ R .G + R .T = 3 := by decide

/-- The pairing map, Watson-Crick. -/
def wc : Base → Base
  | .A => .T | .T => .A | .G => .C | .C => .G

/-- **Theorem 1, in general over the pairing map.** Not three instances: the
    invariant holds for every base, which is the statement the suite boxes. -/
theorem constant_width_all (b : Base) : R b + R (wc b) = 3 := by
  cases b <;> decide

/-- A transition preserves the ring class, `ΔR = 0`; a transversion changes it. -/
def isTransition (x y : Base) : Bool := R x = R y

/-- All four bases, as a list. -/
def all : List Base := [.T, .C, .A, .G]

/-- **The step alphabet is nine, not sixteen.** Sixteen ordered pairs of bases
    give only nine distinct exact steps: stay, two transitions, two
    transversions, four diagonals. -/
theorem step_alphabet_card :
    ((all.flatMap (fun x => all.map (fun y => delta x y))).eraseDups).length = 9 := by
  decide

/-- **Theorem 6 — the UUCG tetraloop closes exactly.** The four steps of the
    loop `U → U → C → G → U` sum to `(0,0)`: zero net torsional shear, so the
    hairpin's holonomy is the identity. `U = T` in this lattice. -/
theorem uucg_closes :
    delta .T .T + delta .T .C + delta .C .G + delta .G .T = (0, 0) := by
  decide

/-- **The Watson-Crick step is a pure ring move.** `A→T` and `G→C` both have
    `ΔH = 0`: pairing costs nothing in hydrogen-bonding coordinate, which is
    why the two pair classes sit at constant `H` and the diameter is fixed by
    `R` alone. -/
theorem wc_is_ring_move (b : Base) : (delta b (wc b)).1 = 0 := by
  cases b <;> decide

/-- **The four bases are the corners of a unit square.** Every base has a
    unique `(H,R)`, and the coordinates take exactly two values each — so the
    lattice is `{2,3} × {1,2}` and nothing else. -/
theorem lattice_is_unit_square :
    ((all.map (fun b => (H b, R b))).eraseDups).length = 4 ∧
    ((all.map H).eraseDups).length = 2 ∧
    ((all.map R).eraseDups).length = 2 := by
  decide

/-- **The Z₁₂ pair-rule phase.** `φ(L) = -1`, `φ(R) = +1`, so the pair-rule
    word `L³R³` has phase zero and the seven-fold body plan `(L³R³)⁷` closes
    with no drift. Theorem 14, the arithmetic half. -/
def phase (nL nR : ℤ) : ZMod 12 := ((nR - nL : ℤ) : ZMod 12)

theorem pair_rule_closes : phase 3 3 = 0 := by decide

theorem body_plan_closes : phase (3 * 7) (3 * 7) = 0 := by decide

/-! ## The holonomy halves: Theorems 7, 8, 11 and 14

  Each stated with its full quantifier over `Mat2`. Two of the four close for
  every invertible pair and use nothing about `L`, `R`, `k` or parity: they are
  cancellation. Polyspermy carries content, because `R` has infinite order.
  Theorem 14's zero phase holds in `ℤ`, so in every modulus, and the body-plan
  matrix never returns: the phase returns and the frame does not. Theorem 7 is
  stated as its necessity half only: by `S⁴ = I`, any modulus the phase reading
  identifies divides twelve. -/

/-- `L^k` for any integer `k`. `k ↦ Lk k` is a homomorphism from `(ℤ,+)`
    (`Lk_add`), so these are the integer powers, negative ones included. -/
def Lk (k : ℤ) : Mat2 := ⟨1, 0, k, 1⟩

/-- `R^k` for any integer `k`. -/
def Rk (k : ℤ) : Mat2 := ⟨1, k, 0, 1⟩

theorem Lk_one : Lk 1 = Mat2.L := rfl
theorem Rk_one : Rk 1 = Mat2.R := rfl

theorem Lk_add (m n : ℤ) : Lk m * Lk n = Lk (m + n) := by
  apply Mat2.ext' <;> simp [Mat2.mul_def, Lk]

theorem Rk_add (m n : ℤ) : Rk m * Rk n = Rk (m + n) := by
  apply Mat2.ext' <;> simp [Mat2.mul_def, Rk]; ring

theorem Lk_neg_mul (k : ℤ) : Lk (-k) * Lk k = 1 := by
  apply Mat2.ext' <;> simp [Mat2.mul_def, Lk]

theorem Rk_neg_mul (k : ℤ) : Rk (-k) * Rk k = 1 := by
  apply Mat2.ext' <;> simp [Mat2.mul_def, Rk]

/-- `R^k = I` exactly when `k = 0`: the parabolic has infinite order. -/
theorem Rk_eq_one_iff (k : ℤ) : Rk k = 1 ↔ k = 0 := by
  constructor
  · intro h
    have hb := congrArg Mat2.b h
    simpa [Rk] using hb
  · rintro rfl
    rfl

/-- **Cancellation closes any pair.** For any `A`, `B` with left inverses `A'`,
    `B'`, `A'(AB')B = I`. No hypothesis on what `A` and `B` are. -/
theorem cancel_closes (A A' B B' : Mat2) (hA : A' * A = 1) (hB : B' * B = 1) :
    A' * (A * B') * B = 1 := by
  rw [← Mat2.mul_assoc', hA, Mat2.one_mul', hB]

/-- **Theorem 11, syngamy.** `L⁻ᵏ(LᵏR⁻ᵏ)Rᵏ = I` for every integer `k`, as the
    suite states. It is `cancel_closes` at `A = Lᵏ`, `B = Rᵏ`: the identity
    holds for any two invertible frames and does not use the maternal and
    paternal words being `L`- and `R`-powers. -/
theorem syngamy_closes (k : ℤ) : Lk (-k) * (Lk k * Rk (-k)) * Rk k = 1 :=
  cancel_closes _ _ _ _ (Lk_neg_mul k) (Rk_neg_mul k)

/-- **Theorem 11, polyspermy.** The extra `Rᵏ` leaves exactly `Rᵏ`. -/
theorem polyspermy (k : ℤ) : Lk (-k) * (Lk k * Rk (-k)) * Rk (2 * k) = Rk k := by
  apply Mat2.ext' <;> simp [Mat2.mul_def, Lk, Rk]; ring

/-- **Theorem 11, polyspermy, the half with content.** For every `k ≠ 0` the
    composite is not the identity, because `R` has infinite order. -/
theorem polyspermy_ne_one (k : ℤ) (hk : k ≠ 0) :
    Lk (-k) * (Lk k * Rk (-k)) * Rk (2 * k) ≠ 1 := by
  rw [polyspermy]
  exact fun h => hk ((Rk_eq_one_iff k).1 h)

/-- **Theorem 8, cognate locking.** `(w_A⁻¹w_A)(w_B⁻¹w_B) = I` for **every**
    pair on the determinant-one shell. The cognate condition `w_B = P w_A P`
    is not a hypothesis: the product closes for any `w_A`, `w_B` whatever, so
    it cannot separate cognate from non-cognate sites. The suite's contrasting
    `Q_sliding ≠ I` is not defined in v1.0 and is not stated here. -/
theorem cognate_closes_any (A B : Mat2) (hA : A.det = 1) (hB : B.det = 1) :
    (Mat2.inv2 A * A) * (Mat2.inv2 B * B) = 1 := by
  rw [Mat2.inv2_mul_of_det A hA, Mat2.inv2_mul_of_det B hB, Mat2.one_mul']

/-- The pair-rule segment `L³R³` as a positive word, `false = L`, `true = R`. -/
def pairRule : Word := [false, false, false, true, true, true]

/-- The body plan `(L³R³)ᵐ`. -/
def bodyPlan : ℕ → Word
  | 0 => []
  | m + 1 => pairRule ++ bodyPlan m

/-- The word phase, `φ(R) = +1`, `φ(L) = -1`, in `ℤ`. No modulus. -/
def wordPhase (w : Word) : ℤ := (w.count true : ℤ) - (w.count false : ℤ)

theorem pairRule_matrix : Word.G pairRule = ⟨1, 3, 3, 10⟩ := by decide

/-- **Theorem 14, the phase.** `(L³R³)ᵐ` has phase zero in `ℤ`, for every `m`. -/
theorem bodyPlan_phase (m : ℕ) : wordPhase (bodyPlan m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : pairRule.count true = 3 := by decide
    have h2 : pairRule.count false = 3 := by decide
    simp only [wordPhase, bodyPlan, List.count_append] at ih ⊢
    push_cast
    rw [h1, h2]
    push_cast
    omega

/-- **Theorem 14's zero carries no information about twelve.** It holds in
    every modulus `n`, twelve included, because it holds in `ℤ`. -/
theorem bodyPlan_phase_every_modulus (n m : ℕ) :
    ((wordPhase (bodyPlan m) : ℤ) : ZMod n) = 0 := by
  rw [bodyPlan_phase]
  simp

/-- **Theorem 14, the frame does not return.** For every `m ≥ 1` the body-plan
    matrix is not the identity. The phase returns and the frame does not: the
    closure is a return at the phase receiver, not of the state. -/
theorem bodyPlan_not_closed (m : ℕ) : Word.G (bodyPlan (m + 1)) ≠ 1 :=
  G_cons_ne_one false ([false, false, true, true, true] ++ bodyPlan m)

/-- The suite's seven-fold body plan, the instance. -/
theorem bodyPlan_seven_not_closed : Word.G (bodyPlan 7) ≠ 1 := bodyPlan_not_closed 6

/-- The four letters with inverses. Theorem 7's topoisomerases need `R⁻¹`. -/
inductive Letter where
  | R | L | Ri | Li
deriving DecidableEq, Repr

def Letter.mat : Letter → Mat2
  | .R => Mat2.R | .L => Mat2.L | .Ri => Rk (-1) | .Li => Lk (-1)

def Letter.phase : Letter → ℤ
  | .R => 1 | .L => -1 | .Ri => -1 | .Li => 1

/-- A signed word evaluated left to right. -/
def evalS : List Letter → Mat2
  | [] => 1
  | x :: w => x.mat * evalS w

/-- Its phase, in `ℤ`. -/
def phaseS : List Letter → ℤ
  | [] => 0
  | x :: w => x.phase + phaseS w

/-- **Theorem 7's topoisomerase quanta**, at the word level: type I moves the
    phase by `±1`, type II by `±2`. True by the definition of the phase. -/
theorem topo_phases :
    phaseS [.R] = 1 ∧ phaseS [.Ri] = -1 ∧
    phaseS [.R, .R] = 2 ∧ phaseS [.Ri, .Ri] = -2 := by decide

/-- `S = R⁻¹ L R⁻¹`, the quarter turn, phase `-3`. -/
def sWord : List Letter := [.Ri, .L, .Ri]

theorem sWord_is_S : evalS sWord = ⟨0, -1, 1, 0⟩ := by decide
theorem sWord_phase : phaseS sWord = -3 := by decide

/-- `S⁴`, a word of length twelve. -/
def fourS : List Letter := sWord ++ sWord ++ sWord ++ sWord

theorem fourS_closes : evalS fourS = 1 := by decide
theorem fourS_phase : phaseS fourS = -12 := by decide

/-- **Theorem 7, necessity half: the phase modulus divides twelve.** If the phase is to be read
  off the
    matrices at all, with `φ(R) = +1` and `φ(L) = -1`, then whatever integer
    `n` the reading identifies must divide the phase of every word evaluating
    to `I`, and `S⁴` is such a word with phase `-12`. So `n` divides twelve.
    Stated as integer divisibility rather than in `ZMod n`: the residue is the
    reception, the divisibility is the substrate.

    This is the necessity half only. That twelve suffices, that `φ` is well
    defined on all of `SL(2,ℤ)`, is not claimed here. A twelve-class character
    with `T ↦ 1` exists (`Closure12.congruence` in `Winding.lean`, built for
    audit E1-B11, 2026-09-29); that `phaseS` factors through it is not stated.
    *(Until 2026-09-29 this line called sufficiency "the open `Closure12` gap".)* -/
theorem phase_modulus_dvd_twelve (n : ℤ)
    (h : ∀ w : List Letter, evalS w = 1 → n ∣ phaseS w) : n ∣ 12 := by
  have h12 := h fourS fourS_closes
  rw [fourS_phase] at h12
  exact Int.dvd_neg.1 h12

/-! ## Theorem 9: the CpG invariants

  The bracket as written is antisymmetry of `δ` and closes for every ordered
  pair. "Reverse" has two strand readings that coincide at CpG, and a third,
  the complement read 5'→3', under which CpG does not close. Deamination is the
  half with content. MeCP2's "conjugate frame" is not defined in v1.0 and is
  not stated here. -/

/-- **Theorem 9, the CpG duplex bracket, as the suite writes it.** -/
theorem cpg_bracket : delta .C .G + delta .G .C = (0, 0) := by decide

/-- **The bracket is antisymmetry.** Reversal closes every ordered pair, so it
    cannot single out CpG. -/
theorem bracket_reverse (x y : Base) : delta x y + delta y x = (0, 0) := by
  cases x <;> cases y <;> decide

/-- **The complement strand, aligned.** Pairing keeps `H` and sends `R` to
    `3 - R`, so the bracket closes exactly when the step has `ΔH = 0`: eight of
    sixteen dinucleotides, CpG among them. -/
theorem bracket_aligned_iff (x y : Base) :
    delta x y + delta (wc x) (wc y) = (0, 0) ↔ H x = H y := by
  cases x <;> cases y <;> decide

/-- **The complement strand, read 5'→3'.** Closes exactly when `ΔR = 0`. -/
theorem bracket_antiparallel_iff (x y : Base) :
    delta x y + delta (wc y) (wc x) = (0, 0) ↔ R x = R y := by
  cases x <;> cases y <;> decide

/-- **CpG is its own antiparallel complement**, so under that reading its
    bracket doubles instead of closing. -/
theorem cpg_antiparallel : delta (wc .G) (wc .C) = delta .C .G ∧
    delta .C .G + delta (wc .G) (wc .C) = (0, 2) := by decide

/-- **Theorem 9, deamination, as written.** `5mC → T` turns `δ(C,G) = (0,1)`
    into `δ(T,G) = (1,1)`, and `τ` from one to two. -/
theorem deamination_cpg : delta .C .G = (0, 1) ∧ delta .T .G = (1, 1) ∧
    tau .C .G = 1 ∧ tau .T .G = 2 := by decide

/-- **Deamination, over every following base.** `C → T` lowers `H` by one at
    the step's start, so `τ` rises by one exactly when the next base is strong
    (`C`, `G`) and falls by one when it is weak (`A`, `T`). The rise at CpG is
    the half with content; at CpA the same lesion lowers the tension. -/
theorem deamination_tau (y : Base) :
    tau .T y = tau .C y + (if H y = 3 then 1 else -1) := by
  cases y <;> decide

/-- **Theorem 9's diameter is Theorem 1.** A transition keeps `R`, so the
    mismatch it leaves against the old partner still sums to three rings. -/
theorem transition_mismatch_width (b b' : Base) (h : R b' = R b) :
    R b' + R (wc b) = 3 := by
  rw [h]; exact constant_width_all b

theorem deamination_width : R .T + R .G = 3 := transition_mismatch_width .C .T rfl

/-! ## Theorem 3: the 268 junction contexts

  The suite counts 180 of 268 "synonymous junction contexts" as kinematic
  discontinuities, split 46 compound, 80 boundary diagonal only, 54 internal
  stall only. The Logic Spine's restatement pins the reading: a context
  *introduces or eliminates* a stall `δ₂ = (0,0)` or a boundary diagonal
  `τ(δ_bnd) = 2`. That is symmetric, so a context is an unordered synonymous
  single-base pair of sense codons with the next codon's first base, and the
  code has exactly 67 such pairs: `67 × 4 = 268`, so the text does fix it.

  Under that reading the counts are 62, 64, 62, total 188, and the split
  cannot be the suite's: the four bases are a unit square's corners, so a
  third-base change alters the diagonal at exactly two of the four next bases,
  and the stall does not depend on the next base at all. Compound equals stall
  only for every third-base pair. What keeps it equal over the whole code is
  Theorem 2: a middle-base pair would add stall-only contexts and nothing else,
  and among amino acids there are none. -/

/-- The twenty amino acids and Stop. -/
inductive AA where
  | Phe | Leu | Ile | Met | Val | Ser | Pro | Thr | Ala | Tyr
  | His | Gln | Asn | Lys | Asp | Glu | Cys | Trp | Arg | Gly | Stop
deriving DecidableEq, Repr

/-- The standard genetic code. -/
def code : Base → Base → Base → AA
  | .T, .T, .T => .Phe | .T, .T, .C => .Phe | .T, .T, .A => .Leu | .T, .T, .G => .Leu
  | .T, .C, _ => .Ser
  | .T, .A, .T => .Tyr | .T, .A, .C => .Tyr | .T, .A, .A => .Stop | .T, .A, .G => .Stop
  | .T, .G, .T => .Cys | .T, .G, .C => .Cys | .T, .G, .A => .Stop | .T, .G, .G => .Trp
  | .C, .T, _ => .Leu
  | .C, .C, _ => .Pro
  | .C, .A, .T => .His | .C, .A, .C => .His | .C, .A, .A => .Gln | .C, .A, .G => .Gln
  | .C, .G, _ => .Arg
  | .A, .T, .T => .Ile | .A, .T, .C => .Ile | .A, .T, .A => .Ile | .A, .T, .G => .Met
  | .A, .C, _ => .Thr
  | .A, .A, .T => .Asn | .A, .A, .C => .Asn | .A, .A, .A => .Lys | .A, .A, .G => .Lys
  | .A, .G, .T => .Ser | .A, .G, .C => .Ser | .A, .G, .A => .Arg | .A, .G, .G => .Arg
  | .G, .T, _ => .Val
  | .G, .C, _ => .Ala
  | .G, .A, .T => .Asp | .G, .A, .C => .Asp | .G, .A, .A => .Glu | .G, .A, .G => .Glu
  | .G, .G, _ => .Gly

abbrev Codon := Base × Base × Base

def aa (c : Codon) : AA := code c.1 c.2.1 c.2.2

def Base.idx : Base → ℕ
  | .T => 0 | .C => 1 | .A => 2 | .G => 3

def codons : List Codon :=
  all.flatMap fun x => all.flatMap fun y => all.map fun z => (x, y, z)

/-- The single-base neighbours of `c` carrying a later base, tagged with the
    position changed: each unordered pair appears once. -/
def up (c : Codon) : List (Codon × ℕ) :=
  (all.filter (fun b => c.1.idx < b.idx)).map (fun b => ((b, c.2.1, c.2.2), 0)) ++
  (all.filter (fun b => c.2.1.idx < b.idx)).map (fun b => ((c.1, b, c.2.2), 1)) ++
  (all.filter (fun b => c.2.2.idx < b.idx)).map (fun b => ((c.1, c.2.1, b), 2))

/-- Unordered synonymous single-base pairs of sense codons, with the position. -/
def synPairs : List (Codon × Codon × ℕ) :=
  codons.flatMap fun c => (up c).filterMap fun d =>
    if aa c = aa d.1 ∧ aa c ≠ .Stop then some (c, d.1, d.2) else none

/-- The internal stall `δ₂ = (0,0)`. -/
def stall (c : Codon) : Bool := decide (c.2.1 = c.2.2)

/-- The boundary diagonal, `|ΔH| = 1 ∧ |ΔR| = 1`. -/
def diag (x y : Base) : Bool := decide (H x ≠ H y) && decide (R x ≠ R y)

theorem diag_iff_tau (x y : Base) : diag x y = true ↔ tau x y = 2 := by
  cases x <;> cases y <;> decide

def stallChanges (p : Codon × Codon × ℕ) : Bool := stall p.1 != stall p.2.1

def diagChanges (p : Codon × Codon × ℕ) (n : Base) : Bool :=
  diag p.1.2.2 n != diag p.2.1.2.2 n

def contexts : List ((Codon × Codon × ℕ) × Base) :=
  synPairs.flatMap fun p => all.map fun n => (p, n)

def compound : ℕ := contexts.countP fun q => stallChanges q.1 && diagChanges q.1 q.2
def boundaryOnly : ℕ := contexts.countP fun q => !stallChanges q.1 && diagChanges q.1 q.2
def stallOnly : ℕ := contexts.countP fun q => stallChanges q.1 && !diagChanges q.1 q.2

/-- **The 268 is fixed by the code.** 67 unordered synonymous pairs, four next
    bases each. -/
theorem synPairs_card : synPairs.length = 67 ∧ contexts.length = 268 := by decide +kernel

/-- **Theorem 2, among amino acids, from the same table.** Four synonymous
    pairs change the first base, none the middle, 63 the third. -/
theorem synPairs_by_position :
    (synPairs.filter (·.2.2 = 0)).length = 4 ∧ (synPairs.filter (·.2.2 = 1)).length = 0 ∧
    (synPairs.filter (·.2.2 = 2)).length = 63 := by decide +kernel

/-- **Theorem 3, the census.** 62 compound, 64 boundary only, 62 stall only. -/
theorem theorem3_census : compound = 62 ∧ boundaryOnly = 64 ∧ stallOnly = 62 := by
  decide +kernel

/-- **Theorem 3 fails as written**: 188 of 268, not 180, and not 46, 80, 54. -/
theorem theorem3_total : compound + boundaryOnly + stallOnly = 188 := by decide +kernel

theorem theorem3_not_as_written :
    ¬(compound = 46 ∧ boundaryOnly = 80 ∧ stallOnly = 54) ∧
    compound + boundaryOnly + stallOnly ≠ 180 := by decide +kernel

/-- **The unit square forces the diagonal.** For any two distinct bases, the
    diagonal status of the step to the next base differs at exactly two of the
    four next bases. -/
theorem diag_changes_at_two (b b' : Base) (h : b ≠ b') :
    (all.filter fun n => diag b n != diag b' n).length = 2 := by
  cases b <;> cases b' <;> first | exact absurd rfl h | decide

/-- **Compound equals stall only, for every third-base pair**, synonymous or
    not: the stall does not see the next base, and the diagonal changes at two
    of four. -/
theorem third_base_balanced (x y z z' : Base) (h : z ≠ z') :
    (all.filter fun n => stallChanges ((x, y, z), (x, y, z'), 2) &&
        diagChanges ((x, y, z), (x, y, z'), 2) n).length =
    (all.filter fun n => stallChanges ((x, y, z), (x, y, z'), 2) &&
        !diagChanges ((x, y, z), (x, y, z'), 2) n).length := by
  cases x <;> cases y <;> cases z <;> cases z' <;> first | exact absurd rfl h | decide

/-- **A first-base pair is never a discontinuity**: it moves neither `δ₂` nor
    `δ_bnd`. -/
theorem first_base_silent (x x' y z n : Base) :
    stallChanges ((x, y, z), (x', y, z), 0) = false ∧
    diagChanges ((x, y, z), (x', y, z), 0) n = false := by
  simp [stallChanges, diagChanges, stall]

/-- **The suite's worked instance holds.** MDR1 `ATC → ATT`, both Ile, before
    `G`: the stall is introduced and so is the diagonal, a compound context. -/
theorem mdr1_compound :
    aa (.A, .T, .C) = aa (.A, .T, .T) ∧ stall (.A, .T, .C) = false ∧
    stall (.A, .T, .T) = true ∧ diag .C .G = false ∧ diag .T .G = true := by decide

/-! ## Theorem 10: overlapping genes

  The suite states `δ₁⁽¹⁾ ≡ δ₂⁽⁰⁾` and `δ₂⁽¹⁾ ≡ δ_bnd⁽⁰⁾` for phiX174's gene B
  inside gene A. For a sequence `s` read in frame `f`, codon `i` is bases
  `3i+f, 3i+f+1, 3i+f+2`; its internal steps are `δ₁`, `δ₂` and the step to the
  next codon is `δ_bnd`. The identity is re-indexing and holds for every
  sequence, so it says nothing about the phage. -/

/-- First internal step of codon `i` in frame `f`. -/
def d1 (s : ℕ → Base) (f i : ℕ) : ℤ × ℤ := delta (s (3 * i + f)) (s (3 * i + f + 1))

/-- Second internal step. -/
def d2 (s : ℕ → Base) (f i : ℕ) : ℤ × ℤ := delta (s (3 * i + f + 1)) (s (3 * i + f + 2))

/-- The boundary step into the next codon. -/
def dbnd (s : ℕ → Base) (f i : ℕ) : ℤ × ℤ := delta (s (3 * i + f + 2)) (s (3 * i + f + 3))

/-- **The suite's identity, for any sequence.** One base later, the first
    internal step is the second, and the second is the boundary. -/
theorem frame_plus_one (s : ℕ → Base) (f i : ℕ) :
    d1 s (f + 1) i = d2 s f i ∧ d2 s (f + 1) i = dbnd s f i := ⟨rfl, rfl⟩

/-- **Two bases later**, the first internal step is the boundary and the
    second is the next codon's first. -/
theorem frame_plus_two (s : ℕ → Base) (f i : ℕ) :
    d1 s (f + 2) i = dbnd s f i ∧ d2 s (f + 2) i = d1 s f (i + 1) := by
  constructor <;> simp only [d1, d2, dbnd] <;> congr 2 <;> omega

/-- The suite's boundary step `G → T`. -/
theorem delta_G_T : delta .G .T = (-1, -1) := by decide

/-! ## Theorems 13 and 15: the morula and the limb

  Both read nodes of the walk, `r w`. The mirror of a word reads the
  reciprocal, for every word, and fixes only the empty word; so a mirror-closed
  set of odd size must contain the root, and five digits at one depth cannot
  be mirror-closed. -/

open Frame Word

/-- A word reads the node `p:q`. -/
abbrev reads (w : Word) (p q : ℕ) : Prop := (r w).p = p ∧ (r w).q = q

/-- The node is read off the matrix: `p = a + b`. -/
theorem r_p (w : Word) : ((r w).p : ℤ) = (Word.G w).a + (Word.G w).b := by
  rw [← toMat2_walk_empty w]
  simp [r, addressed, mid, Pres.mediant, toMat2]

/-- And `q = c + d`. -/
theorem r_q (w : Word) : ((r w).q : ℤ) = (Word.G w).c + (Word.G w).d := by
  rw [← toMat2_walk_empty w]
  simp [r, addressed, mid, Pres.mediant, toMat2]

theorem mirror_mirror (w : Word) : shadow (shadow w) = w := by
  induction w <;> simp_all [shadow]

/-- **The mirror fixes only the empty word**: it flips the first letter. -/
theorem mirror_fixed_iff (w : Word) : shadow w = w ↔ w = [] := by
  cases w with
  | nil => simp
  | cons b w => cases b <;> simp [shadow]

/-- `P G(w) P` reverses the four entries. -/
theorem G_mirror_entries (w : Word) :
    (Word.G (shadow w)).a = (Word.G w).d ∧ (Word.G (shadow w)).b = (Word.G w).c ∧
    (Word.G (shadow w)).c = (Word.G w).b ∧ (Word.G (shadow w)).d = (Word.G w).a := by
  rw [G_shadow]
  simp [Mat2.mul_def, Mat2.P]

/-- **The mirror word reads the reciprocal, for every word.** Theorem 13's
    `(3:5)·(5:3) = 1` and Theorem 15's dimer products are instances. -/
theorem r_mirror (w : Word) :
    (r (shadow w)).p = (r w).q ∧ (r (shadow w)).q = (r w).p := by
  obtain ⟨ha, hb, hc, hd⟩ := G_mirror_entries w
  have h1 := r_p (shadow w)
  have h2 := r_q (shadow w)
  have h3 := r_p w
  have h4 := r_q w
  constructor <;> omega

/-- **Theorem 13, the two alternating words.** `LRL` reads `3:5 = [0;1,1,2]`,
    `RLR` reads `5:3 = [1;1,2]`, and each is the other's mirror. -/
theorem morula_nodes :
    reads [false, true, false] 3 5 ∧ reads [true, false, true] 5 3 ∧
    shadow [false, true, false] = [true, false, true] := by decide

/-- **"Alternating words reach maximal depth", over all eight.** Every
    length-three word reads a node with `p + q ≤ 8`, and it is exactly eight
    exactly when the word alternates: two of the eight cells. -/
theorem morula_alternating_max (a b c : Bool) :
    (r [a, b, c]).p + (r [a, b, c]).q ≤ 8 ∧
    ((r [a, b, c]).p + (r [a, b, c]).q = 8 ↔ (a ≠ b ∧ b ≠ c)) := by
  revert a b c; decide

/-- **Theorem 15, the five digits.** `1:5` and `5:1` are four letters deep;
    `2:5`, `3:5` and `5:2` are three. -/
theorem digit_nodes :
    reads [false, false, false, false] 1 5 ∧ reads [true, true, true, true] 5 1 ∧
    reads [false, false, true] 2 5 ∧ reads [false, true, false] 3 5 ∧
    reads [true, true, false] 5 2 := by decide

/-- **The five digits do not sit at one depth.** No word of length four reads
    `2:5`, `3:5` or `5:2`; no word of length three reads `1:5` or `5:1`. -/
theorem digits_two_depths :
    (∀ a b c d : Bool, ¬reads [a, b, c, d] 2 5 ∧ ¬reads [a, b, c, d] 3 5 ∧
      ¬reads [a, b, c, d] 5 2) ∧
    (∀ a b c : Bool, ¬reads [a, b, c] 1 5 ∧ ¬reads [a, b, c] 5 1) := by
  decide

/-- **Digit III is not self-reciprocal.** `3:5`'s mirror reads `5:3`, which is
    none of the five, so the hand as listed is not mirror-closed. -/
theorem digit_three_not_self_reciprocal :
    shadow [false, true, false] ≠ [false, true, false] ∧
    reads (shadow [false, true, false]) 5 3 := by decide

/- 2026-09-22: the three mirror-closure theorems below were stated over `Finset Word`; `Finset`'s
   membership instance is classical in this Mathlib, so every such statement carried
   `Classical.choice`. They are now stated over duplicate-free lists, with the same content
   (a finite family of words closed under the mirror), and are choice-free. -/

/-- Remove `w` from a list (every occurrence; exactly one on a duplicate-free list). Written with
    `filter` and `decide` so that its lemmas stay off `Classical.choice`, which `List.erase`'s
    library lemmas (`List.length_erase_of_mem`, `List.mem_erase_of_ne`) reach. -/
def rm (w : Word) (l : List Word) : List Word := l.filter fun x => decide (x ≠ w)

theorem mem_rm {x w : Word} {l : List Word} : x ∈ rm w l ↔ x ∈ l ∧ x ≠ w := by
  simp [rm]

theorem nodup_rm {w : Word} {l : List Word} (h : l.Nodup) : (rm w l).Nodup :=
  List.Nodup.filter _ h

theorem rm_of_not_mem {w : Word} : ∀ {l : List Word}, w ∉ l → rm w l = l
  | [], _ => rfl
  | a :: t, h => by
    have ha : a ≠ w := fun e => h (e ▸ List.mem_cons_self ..)
    have ht : w ∉ t := fun m => h (List.mem_cons_of_mem a m)
    unfold rm
    rw [List.filter_cons_of_pos (p := fun x => decide (x ≠ w)) (decide_eq_true ha)]
    exact congrArg (a :: ·) (rm_of_not_mem ht)

theorem length_rm_of_mem {w : Word} : ∀ {l : List Word}, l.Nodup → w ∈ l →
    (rm w l).length + 1 = l.length
  | [], _, hw => nomatch hw
  | a :: t, hnd, hw => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    by_cases e : a = w
    · subst e
      unfold rm
      rw [List.filter_cons_of_neg (p := fun x => decide (x ≠ a))
        (fun h => (of_decide_eq_true h) rfl)]
      change (rm a t).length + 1 = t.length + 1
      rw [rm_of_not_mem ha]
    · have hw' : w ∈ t := by
        rcases List.mem_cons.mp hw with h | h
        · exact absurd h.symm e
        · exact h
      have ih := length_rm_of_mem ht hw'
      unfold rm at ih ⊢
      rw [List.filter_cons_of_pos (p := fun x => decide (x ≠ w)) (decide_eq_true e),
        List.length_cons, List.length_cons]
      omega

/-- **A mirror-closed family without the root is even**, on duplicate-free lists: the mirror is
    an involution fixing only the empty word, so the rest pair off. -/
theorem mirror_closed_even : ∀ (n : ℕ) (l : List Word), l.Nodup → l.length = n →
    (∀ w ∈ l, shadow w ∈ l) → [] ∉ l → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hnd hn hs h0
    cases l with
    | nil => subst hn; exact ⟨0, rfl⟩
    | cons w t =>
      have hw : w ∈ w :: t := List.mem_cons_self ..
      have hne : shadow w ≠ w := fun e => h0 ((mirror_fixed_iff w).1 e ▸ hw)
      have hsw : shadow w ∈ w :: t := hs w hw
      have hnd1 : (rm w (w :: t)).Nodup := nodup_rm hnd
      have hsw1 : shadow w ∈ rm w (w :: t) := mem_rm.mpr ⟨hsw, hne⟩
      have hlen : (rm (shadow w) (rm w (w :: t))).length + 2 = n := by
        have e1 := length_rm_of_mem hnd hw
        have e2 := length_rm_of_mem hnd1 hsw1
        omega
      have hclosed : ∀ v ∈ rm (shadow w) (rm w (w :: t)),
          shadow v ∈ rm (shadow w) (rm w (w :: t)) := by
        intro v hv
        obtain ⟨hv12, hv3⟩ := mem_rm.mp hv
        obtain ⟨hv1, hv2⟩ := mem_rm.mp hv12
        refine mem_rm.mpr ⟨mem_rm.mpr ⟨hs v hv1, ?_⟩, ?_⟩
        · intro e; exact hv3 (by rw [← e, mirror_mirror])
        · intro e
          exact hv2 (by have := congrArg shadow e; rwa [mirror_mirror, mirror_mirror] at this)
      have h0r : [] ∉ rm (shadow w) (rm w (w :: t)) := fun h => h0 (mem_rm.mp (mem_rm.mp h).1).1
      rw [← hlen]
      exact (ih _ (by omega) _ (nodup_rm hnd1) rfl hclosed h0r).add ⟨1, rfl⟩

theorem mirror_closed_odd_has_root (l : List Word) (hnd : l.Nodup)
    (hs : ∀ w ∈ l, shadow w ∈ l) (hodd : Odd l.length) : [] ∈ l := by
  by_cases h0 : [] ∈ l
  · exact h0
  · obtain ⟨k, hk⟩ := mirror_closed_even _ l hnd rfl hs h0
    obtain ⟨m, hm⟩ := hodd
    omega

theorem mirror_closed_one_depth_even (l : List Word) (hnd : l.Nodup) (d : ℕ) (hd : 0 < d)
    (hlen : ∀ w ∈ l, w.length = d) (hs : ∀ w ∈ l, shadow w ∈ l) : Even l.length :=
  mirror_closed_even _ l hnd rfl hs (fun h => by have := hlen [] h; simp at this; omega)


/-! ## Theorem 4: the ribosomal speedometer

`v_transloc(k) ∝ 1 / Z_ribo(k)`. The suite defines `Z_ribo` nowhere: the
abstract names it and credits it with Theorem 3's percentage, which is a
citation rather than a definition. No constant is chosen here. What is
checkable without one is the two worked instances and what they force.
-/

/-- The stall at the **first** internal step, `δ₁ = (0,0)`, i.e. `b₁ = b₂`.
    Theorem 3 scores `stall`, which is the second step; Theorem 4's CFTR
    instance is about this one, and the suite never distinguishes them. -/
def stall1 (c : Codon) : Bool := decide (c.1 = c.2.1)

/-- **CFTR Leu558, both codons.** Native `TTA` has `δ₁ = (0,0)`, `δ₂ = (0,1)`;
    the synonymous `CTC` has `δ₁ = (-1,0)`, `δ₂ = (+1,0)`, the pair the suite
    prints, and stalls at neither step. -/
theorem cftr_steps :
    delta Base.T Base.T = (0, 0) ∧ delta Base.T Base.A = (0, 1) ∧
    delta Base.C Base.T = (-1, 0) ∧ delta Base.T Base.C = (1, 0) := by decide

/-- **MDR1 Ile1145, both codons.** Native `ATC` stalls at neither step; the
    mutant `ATT` stalls at `δ₂`. -/
theorem mdr1_steps :
    delta Base.A Base.T = (0, -1) ∧ delta Base.T Base.C = (1, 0) ∧
    delta Base.T Base.T = (0, 0) := by decide

/-- **The speedometer's two instances differ only in where the stall sits.**
    Both stalls are the vector `(0,0)` — that is what `stall`/`stall1` decide —
    but CFTR's is native and protective at `δ₁` while MDR1's is the mutation
    and pathogenic at `δ₂`. One vector, two signs of effect. So `Z_ribo` is not
    a function of the step: it would take one value where the biology assigns
    two. Only the codon position separates them, and the suite never says the
    position matters. -/
theorem speedometer_stalls_differ_only_in_position :
    stall1 (Base.T, Base.T, Base.A) = true ∧
    stall (Base.T, Base.T, Base.A) = false ∧
    stall1 (Base.A, Base.T, Base.T) = false ∧
    stall (Base.A, Base.T, Base.T) = true := by decide

/-- **Theorem 3 scores every first-base synonymous pair clean.** Its criterion
    reads `δ₂` and the boundary step, both functions of `b₂`, `b₃` and the next
    base, so a first-base substitution cannot move either — for all four such
    pairs and all four next bases, whatever `δ₁` does. The `δ₁` channel is
    outside the 268 contexts' reach, not merely rare in them. -/
theorem first_base_pairs_score_clean :
    (synPairs.filter (·.2.2 = 0)).all
      (fun p => !stallChanges p && all.all (fun n => !diagChanges p n)) = true := by
  decide +kernel

/-- **The `δ₁` channel is not empty: two of the four first-base pairs move it.**
    `TTA ↔ CTA` and `TTG ↔ CTG`, both Leucine. `TTA → CTA` is the
    single-base change that removes exactly the stall the CFTR instance is
    about; the suite reached past it for the two-base `TTA → CTC`. -/
theorem first_base_delta1_stalls :
    (synPairs.filter (fun p => p.2.2 = 0 && (stall1 p.1 != stall1 p.2.1))).length
      = 2 := by decide +kernel

/-- Reversal of an ordered synonymous change. -/
def swapPair (p : Codon × Codon × ℕ) : Codon × Codon × ℕ := (p.2.1, p.1, p.2.2)

/-- The ordered synonymous single-base changes: each unordered pair both ways. -/
def orderedSyn : List (Codon × Codon × ℕ) := synPairs ++ synPairs.map swapPair

/-- **Stalling is symmetric in the step**, so reversal carries a stall gain onto
    a stall loss and fixes neither. -/
theorem stallChanges_swap (p : Codon × Codon × ℕ) :
    stallChanges (swapPair p) = stallChanges p := by
  cases h1 : stall p.1 <;> cases h2 : stall p.2.1 <;>
    simp [stallChanges, swapPair, h1, h2]

/-- **Gain and loss are in exact bijection, in both channels.** Of the 134
    ordered synonymous single-base changes, 31 introduce a `δ₂` stall and 31
    remove one; 2 introduce a `δ₁` stall and 2 remove one. Reversal is the
    bijection. So nothing in the lattice ranks introduction against removal:
    the sign of the effect is not a lattice quantity, which is why the suite's
    own two instances sit on opposite sides of one orbit and are both
    pathogenic. -/
theorem stall_gains_eq_losses :
    orderedSyn.length = 134 ∧
    (orderedSyn.countP fun p => !stall p.1 && stall p.2.1) = 31 ∧
    (orderedSyn.countP fun p => stall p.1 && !stall p.2.1) = 31 ∧
    (orderedSyn.countP fun p => !stall1 p.1 && stall1 p.2.1) = 2 ∧
    (orderedSyn.countP fun p => stall1 p.1 && !stall1 p.2.1) = 2 := by
  decide +kernel

/-! ## Theorem 5: the relational splicing barcode

The suite:

> **3' Acceptor Barcode:** Pyrimidine Glide `(ΔR = 0)` → Purine Lift `(−1,+1)`
> → Junction Dwell `(0,0)`.
> **5' Donor Barcode:** Junction Dwell `(0,0)` → Diagonal Plunge `(−1,−1)`.
> Pseudo-splice sites fail due to the lack of the sequential
> `(0,0) → (−1,−1)` gate. Post-splicing exon ligation (`G → G`) carries zero
> relational tension: `δ = (0,0)`.

A step vector determines its endpoint from its start, so a barcode of `n`
consecutive steps is not a pattern over sequences: it is a set of `(n+1)`-base
words, and the set can be enumerated. Both are enumerated below.
-/

/-- All `n`-base words, in the obvious order. -/
def words : ℕ → List (List Base)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun w => all.map fun b => b :: w

/-- The step sequence of a word: `n` steps for `n+1` bases. -/
def steps : List Base → List (ℤ × ℤ)
  | b :: c :: rest => delta b c :: steps (c :: rest)
  | _ => []

/-- The donor barcode as a predicate on words: dwell then plunge. -/
def donorBarcode (w : List Base) : Bool := steps w == [(0, 0), (-1, -1)]

/-- The acceptor barcode read as three consecutive steps: a `ΔR = 0` glide,
    then the lift, then the dwell. The glide's `ΔH` is unconstrained, which is
    what the suite writes. -/
def acceptorBarcode (w : List Base) : Bool :=
  match steps w with
  | [g, l, d] => g.2 == 0 && l == (-1, 1) && d == (0, 0)
  | _ => false

/-- **The donor gate is one trinucleotide, `GGT`, and nothing else.** Exactly
    one of the 64 three-base words realizes `(0,0) → (−1,−1)`. So the "gate"
    carries no more information than the 3-mer: the dwell forces the base
    before the plunge to equal the base before it, and the plunge is only ever
    `G → T`. -/
theorem donor_gate_is_GGT :
    (words 3).filter donorBarcode = [[.G, .G, .T]] ∧ (words 3).length = 64 := by
  decide +kernel

/-- **`GGT` puts the junction where the GT-AG rule puts it.** The exon's last
    base is `G`, the intron's first two are `G T`: the dwell straddles the
    junction and the plunge is the intron's own first step. The donor barcode
    is therefore the GT rule plus one extra demand, that the exon end in `G`.
    This is the half of Theorem 5 that is internally consistent. -/
theorem donor_gate_junction :
    delta Base.G Base.G = (0, 0) ∧ delta Base.G Base.T = (-1, -1) := by decide

/-- **The acceptor barcode, read as three consecutive steps, admits exactly
    two words, `TCAA` and `CCAA`** — of 256. Both end `C A | A`. Neither ends
    the intron in `A G`, so the contiguous reading of the 3' barcode
    contradicts the AG rule that the suite's own donor barcode and hierarchy
    table assume. -/
theorem acceptor_barcode_forces_CAA :
    (words 4).filter acceptorBarcode = [[.T, .C, .A, .A], [.C, .C, .A, .A]] ∧
      (words 4).length = 256 := by
  decide +kernel

/-- **The canonical acceptor `C A G | G` is four steps, not three.** Its step
    sequence is glide, lift, `(+1,0)`, dwell: between the Purine Lift and the
    Junction Dwell sits `δ(A, G) = (+1, 0)`, which the barcode does not list.
    So the printed arrows are not composition — the barcode names three
    non-adjacent steps of a four-step window. -/
theorem canonical_acceptor_has_an_unlisted_step :
    steps [.T, .C, .A, .G, .G] = [(1, 0), (-1, 1), (1, 0), (0, 0)] ∧
    steps [.C, .C, .A, .G, .G] = [(0, 0), (-1, 1), (1, 0), (0, 0)] := by decide

/-- **`ΔR = 0` is not "pyrimidine".** `R` is the ring-volume coordinate, so
    `ΔR = 0` says the ring class did not change, and eight of the sixteen
    ordered pairs satisfy it: the four pyrimidine-pyrimidine steps and the four
    purine-purine steps, in equal number. -/
theorem glide_is_ring_class_not_pyrimidine :
    ((all.flatMap fun x => all.map fun y => (x, y)).filter
      fun p => (delta p.1 p.2).2 == 0).length = 8 ∧
    ((all.flatMap fun x => all.map fun y => (x, y)).filter
      fun p => (delta p.1 p.2).2 == 0 && R p.1 == 1).length = 4 := by
  decide +kernel

/-- **A purine tract and a pyrimidine tract have the same step sequence.** So
    the polypyrimidine tract, the single most diagnostic feature of the 3'
    acceptor site, is invisible to step vectors: `AAAA` and `TTTT` are the same
    walk. Reading it needs the absolute `R` coordinate, which is a value and
    not a relation — an anchor the barcode never declares. -/
theorem poly_purine_and_poly_pyrimidine_are_one_walk :
    steps [.A, .A, .A, .A] = steps [.T, .T, .T, .T] ∧
    steps [.A, .A, .A, .A] = [(0, 0), (0, 0), (0, 0)] := by decide

/-- **The ligation dwell is a consequence, not a third invariant.** If the
    donor barcode holds across the 5' junction then the exon's last base is the
    intron's first, and if the acceptor's dwell holds across the 3' junction
    then the intron's last base is the next exon's first. Given the suite's own
    `GT-AG` termini those two bases are both `G`, so the ligation step is
    `δ(G,G) = (0,0)` with nothing left to check. Stated in general: any two
    bases the two dwells identify ligate at `(0,0)`, whatever they are. -/
theorem ligation_dwell_is_derived :
    ∀ e₁ i e₂ : Base, delta e₁ i = (0, 0) → delta i e₂ = (0, 0) →
      delta e₁ e₂ = (0, 0) := by
  intro e₁ i e₂
  cases e₁ <;> cases i <;> cases e₂ <;> decide

/-- **And the dwell is blind to which base it is.** The donor dwell is
    satisfied by any repeated base, not only `G`: it is `δ(b,b) = (0,0)` for
    all four. What forces `G` in `donor_gate_is_GGT` is the plunge that
    follows, not the dwell itself. -/
theorem dwell_holds_at_every_base : all.all (fun b => delta b b == (0, 0)) = true := by
  decide

end Bio
end RatioSpace
