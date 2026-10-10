/-
Copyright (c) 2026 Kurt Michael Russell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kurt Michael Russell
-/
import RatioSpace.ElementsI.S08.Winding
import RatioSpace.ElementsI.S05.Depth
/-!
  Elements II §2 — Temporal event order from ticks, ancestry, and the event ledger.

  Definitions 2.1 through 2.3, Theorem 2.4, Corollary 2.5 and Separation Rule
  2.6. The first section of Elements II that is construction rather than import,
  and it builds entirely on Elements I: freeness from `Walk.lean`, imbalance and
  `ψ₁₂` from `Winding.lean`, depth from `Depth.lean`.

  Four things here are sharper than the prose, and each is noted at its theorem:

    * **Def 2.2's "not inferred from numerical size" is forcing, not a caution.**
      The book lists three quantities the ancestry order is not read off — a
      ratio, a denominator, an endpoint depth. It is read off *none*: ancestry is
      a partial order with incomparable pairs, and any comparison `f x ≤ f y`
      into a linear order is total. One theorem retires the whole list, and every
      future candidate as well.

    * **Def 2.3's `n ≥ k` is load-bearing, and `ℕ` subtraction would hide it.**
      Truncated subtraction is total: a read at stratum `3` of a record written
      at `5` would report archive age `0`, which is the reading for a
      same-stratum read. The clause "defined only after both event strata are
      specified" is the only thing standing between the definition and a silent
      false equality, so the ordering is carried in the type.

    * **Corollary 2.5's "separately declared map" already has an instance, and it
      is exactly twelve letters long.** The first genuine return in the framework
      is the closure residue of §8: `ψ₁₂(w ++ R¹²) = ψ₁₂(w)` for every `w`. So
      2.5 is not an empty escape clause, and the map it points at is the one
      Elements I built.

    * **Separation Rule 2.6's own escape clause is already discharged for three
      of its pairs.** The rule says no row is substituted for another *without an
      explicit theorem*. The observer-relative matrix `Q` determines the
      continuation length and the directional imbalance, by freeness and by
      `bal_of_G_eq`. Those are the explicit theorems. The rows are not a flat
      list of six mutually blind readings; one of them strictly refines three
      others, and the remaining pairs have non-substitution witnesses or stated
      couplings.

  Everything is computable. No `sorry`, no `axiom`.
-/

namespace RatioSpace
namespace Two

open Mat2 Word Frame Pres

/-! ## Definition 2.1 — Cycle and tick order

    `τ ∈ ℕ₀` indexes completed question cycles; `j ∈ {0,…,h_Q}` indexes temporal
    positions inside one cycle. `Fin (h+1)` is that index set exactly, so a tick
    past the declared horizon cannot be written down. -/

/-- **Definition 2.1.** An event-order label `(τ, j)` for a question of declared
    finite horizon `h`. It is an ordered pair of indices, not a coordinate in an
    independently assumed time manifold: nothing below reads a value off it. -/
structure Tick (h : ℕ) where
  tau : ℕ
  j : Fin (h + 1)
  deriving DecidableEq, Repr

namespace Tick

variable {h : ℕ}

/-- **Definition 2.1.** The initial candidate support, carried at `j = 0`. -/
def start (τ : ℕ) : Tick h := ⟨τ, ⟨0, Nat.succ_pos h⟩⟩

/-- **Definition 2.1.** One application of the temporal advance moves the carrier
    from `j` to `j + 1`. It is guarded by the horizon: the book declares `h_Q`
    finite and indexes only up to it, so there is no advance out of the cycle. -/
def advance (t : Tick h) (hj : (t.j : ℕ) < h) : Tick h :=
  ⟨t.tau, ⟨t.j + 1, by omega⟩⟩

@[simp] theorem advance_tau (t : Tick h) (hj : (t.j : ℕ) < h) :
    (t.advance hj).tau = t.tau := rfl

@[simp] theorem advance_j (t : Tick h) (hj : (t.j : ℕ) < h) :
    ((t.advance hj).j : ℕ) = t.j + 1 := rfl

theorem advance_inj {t s : Tick h} {ht : (t.j : ℕ) < h} {hs : (s.j : ℕ) < h}
    (e : t.advance ht = s.advance hs) : t = s := by
  obtain ⟨τ, j⟩ := t
  obtain ⟨σ, i⟩ := s
  simp only [advance, Tick.mk.injEq, Fin.mk.injEq] at e
  obtain ⟨rfl, hji⟩ := e
  exact congrArg (Tick.mk τ) (Fin.ext (by omega))

/-- One advance is a step inside the cycle: the completed-cycle index never
    moves. Advancing is a position change, not a cycle change. -/
theorem advance_same_cycle (t : Tick h) (hj : (t.j : ℕ) < h) :
    (t.advance hj).tau = t.tau := rfl

/-- **Definition 2.1, the negative half.** Reachability by temporal advance.
    This is the only order on labels that the construction supplies. -/
def Advances : Tick h → Tick h → Prop :=
  Relation.ReflTransGen (fun a b => ∃ hj : (a.j : ℕ) < h, b = a.advance hj)

/-- The advance order never crosses a cycle boundary. Two events in different
    completed cycles are not ordered by anything in Def 2.1; what relates them is
    the event ledger of Def 2.3, which is a different datum. This is what "not a
    coordinate in an independently assumed time manifold" means operationally: a
    global `τ`-and-`j` comparison is available to a reader, but it is not the
    construction's order and no result here uses it. -/
theorem advances_same_cycle {t s : Tick h} (hts : Advances t s) : t.tau = s.tau := by
  induction hts with
  | refl => rfl
  | tail _ hstep ih => obtain ⟨hj, rfl⟩ := hstep; exact ih

/-- The advance order is monotone in the within-cycle index, so it is a genuine
    strict progression and not a cycle. -/
theorem advances_j_le {t s : Tick h} (hts : Advances t s) : (t.j : ℕ) ≤ s.j := by
  induction hts with
  | refl => exact Nat.le_refl _
  | tail _ hstep ih => obtain ⟨hj, rfl⟩ := hstep; simp only [advance_j]; omega

/-- `j` counts advances and nothing else. `atStep τ n` is the label reached from
    the initial support of cycle `τ` after `n` applications of the advance. -/
def atStep (τ n : ℕ) (hn : n ≤ h) : Tick h := ⟨τ, ⟨n, by omega⟩⟩

@[simp] theorem atStep_j (τ n : ℕ) (hn : n ≤ h) :
    ((atStep (h := h) τ n hn).j : ℕ) = n := rfl

@[simp] theorem atStep_tau (τ n : ℕ) (hn : n ≤ h) :
    (atStep (h := h) τ n hn).tau = τ := rfl

/-- The initial candidate support is step zero. -/
theorem start_eq_atStep (τ : ℕ) : (start τ : Tick h) = atStep τ 0 (Nat.zero_le h) := rfl

/-- One advance is one step. Composing the two gives the whole of Def 2.1: the
    label at `j = n` is produced by `n` applications of the advance to the
    initial support, so `j` is a count of operations and not a value read off an
    independently assumed clock. -/
theorem advance_atStep (τ n : ℕ) (hn : n ≤ h) (hj : n < h) :
    (atStep (h := h) τ n hn).advance hj = atStep τ (n + 1) (by omega) := rfl

/-- Every label is the label of some step. -/
theorem exists_atStep (t : Tick h) : t = atStep t.tau (t.j : ℕ) (by omega) := by
  obtain ⟨τ, j⟩ := t
  exact congrArg _ (Fin.ext rfl)

end Tick

/-! ## Definition 2.2 — Occurrence ancestry -/

/-- **Definition 2.2.** `x ≼_anc y` exactly when the retained continuation word
    of `y` extends that of `x`. This is prefix order on words: constructive
    availability, recorded as a word extension. -/
def AncLe (x y : Word) : Prop := x <+: y

/-- **Definition 2.2.** Strict ancestry: the descendant segment is nonempty. -/
def AncLt (x y : Word) : Prop := AncLe x y ∧ x ≠ y

instance decAncLe (x y : Word) : Decidable (AncLe x y) :=
  inferInstanceAs (Decidable (x <+: y))

theorem ancLe_refl (x : Word) : AncLe x x := List.prefix_rfl

theorem ancLe_trans {x y z : Word} (h₁ : AncLe x y) (h₂ : AncLe y z) : AncLe x z :=
  h₁.trans h₂

theorem ancLe_antisymm {x y : Word} (h₁ : AncLe x y) (h₂ : AncLe y x) : x = y :=
  h₁.eq_of_length (Nat.le_antisymm h₁.length_le h₂.length_le)

/-- **Definition 2.2.** "The word `u` is the exact descendant segment from `x` to
    `y`" — and it is exact: the segment is unique, so ancestry carries a datum
    rather than only a fact. -/
theorem segment_unique {x y u u' : Word} (h : y = x ++ u) (h' : y = x ++ u') :
    u = u' := by
  exact List.append_cancel_left (h.symm.trans h')

theorem ancLt_iff {x y : Word} : AncLt x y ↔ ∃ u : Word, u ≠ [] ∧ y = x ++ u := by
  constructor
  · rintro ⟨⟨u, rfl⟩, hne⟩
    refine ⟨u, ?_, rfl⟩
    rintro rfl; exact hne (by simp)
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, ?_⟩
    intro he
    have : x ++ u = x ++ [] := by simpa using he.symm
    exact hu (List.append_cancel_left this)

/-- Ancestry is not total: `L` and `R` are incomparable. -/
theorem ancLe_not_total : ¬ AncLe [false] [true] ∧ ¬ AncLe [true] [false] := by
  constructor <;> decide

/-- **Definition 2.2, the negative half, in its strongest form.**

    The book says the ancestry order "is not inferred from the numerical size of
    a ratio, a denominator, or an endpoint depth." It is inferred from *no*
    numerical size at all. Any assignment of values in a linearly ordered type
    gives a total comparison; ancestry has incomparable pairs. So no such
    function reproduces it, and the three named candidates are three instances of
    one obstruction rather than three separate cautions. -/
theorem anc_not_a_size {α : Type*} [LinearOrder α] (f : Word → α) :
    ¬ ∀ x y : Word, AncLe x y ↔ f x ≤ f y := by
  intro h
  have h₁ : ¬ f [false] ≤ f [true] := fun hf => ancLe_not_total.1 ((h _ _).2 hf)
  have h₂ : ¬ f [true] ≤ f [false] := fun hf => ancLe_not_total.2 ((h _ _).2 hf)
  exact h₁ (le_of_not_ge h₂)

/-- Instance: not the denominator of the addressed presentation. -/
theorem anc_not_denominator : ¬ ∀ x y : Word, AncLe x y ↔ (r x).q ≤ (r y).q :=
  anc_not_a_size fun w => (r w).q

/-- Instance: not the numerator either. -/
theorem anc_not_numerator : ¬ ∀ x y : Word, AncLe x y ↔ (r x).p ≤ (r y).p :=
  anc_not_a_size fun w => (r w).p

/-- Instance: not the Stern-Brocot endpoint depth. -/
theorem anc_not_dSB : ¬ ∀ x y : Word, AncLe x y ↔ Pres.dSB (r x) ≤ Pres.dSB (r y) :=
  anc_not_a_size fun w => Pres.dSB (r w)

/-- Instance: not the continued-fraction length. -/
theorem anc_not_lCF : ¬ ∀ x y : Word, AncLe x y ↔ Pres.lCF (r x) ≤ Pres.lCF (r y) :=
  anc_not_a_size fun w => Pres.lCF (r w)

/-! ## Definition 2.3 — Event ledger and archive age -/

/-- **Definition 2.3.** A record in the append-only ledger. `stratum` is the
    exact temporal event stratum `𝓔^(k)` it entered at; `slot` is its storage
    position within that stratum. Every proposal and annotation produced by one
    temporal advance shares a stratum, "independent of its storage position", so
    `slot` is carried and then never read. -/
structure Record where
  stratum : ℕ
  slot : ℕ
  deriving DecidableEq, Repr

/-- **Definition 2.3.** A reading of a record at a later stratum. The ordering
    `k ≤ n` is a field, not a side condition: see `truncation_would_lie`. -/
structure Reading where
  entry : Record
  n : ℕ
  le : entry.stratum ≤ n

/-- **Definition 2.3.** `a_arch(n, k) = n − k`. -/
def archiveAge (R : Reading) : ℕ := R.n - R.entry.stratum

@[simp] theorem archiveAge_def (R : Reading) : archiveAge R = R.n - R.entry.stratum := rfl

/-- **Separation Rule 2.6, shared datum.** A temporal reading binds the ledger
    record/read event to the retained continuation present at that reading.
    Neither component is recovered by silently substituting the other. -/
structure ContinuedReading where
  reading : Reading
  continuation : Word

/-- A record read at its own stratum has age zero. -/
theorem archiveAge_self (c : Record) : archiveAge ⟨c, c.stratum, Nat.le_refl _⟩ = 0 := by
  simp

/-- **Definition 2.3.** Archive age "does not depend on enumeration within one
    tick": two records entering the same stratum in different storage positions
    have the same age at every reading. -/
theorem archiveAge_slot_free (k s s' n : ℕ) (h : k ≤ n) :
    archiveAge ⟨⟨k, s⟩, n, h⟩ = archiveAge ⟨⟨k, s'⟩, n, h⟩ := rfl

/-- **Definition 2.3.** Archive age "counts intervening recorded advances": it is
    additive across an intermediate stratum. -/
theorem archiveAge_add {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (s : ℕ) :
    archiveAge ⟨⟨k, s⟩, n, hkm.trans hmn⟩
      = archiveAge ⟨⟨m, s⟩, n, hmn⟩ + archiveAge ⟨⟨k, s⟩, m, hkm⟩ := by
  simp only [archiveAge_def]; omega

/-- **Why the ordering is a field.** `ℕ` subtraction is total, so a formalisation
    that dropped `k ≤ n` would compute an archive age for a read that precedes
    the write, and would return `0` — the reading reserved for a same-stratum
    read. A record written at stratum `5` and "read" at stratum `3` would be
    reported as contemporaneous with the reading. The book's clause "archive age
    is defined only after both event strata are specified" is the only thing
    standing between Def 2.3 and that silent false equality. -/
theorem truncation_would_lie : (3 : ℕ) - 5 = 0 ∧ (3 : ℕ) - 3 = 0 ∧ (3 : ℕ) ≠ 5 := by
  decide

/-! ## Theorem 2.4 — Nonempty positive continuation changes the word and the matrix -/

/-- **Theorem 2.4.** Status: Derived result. No nonempty positive continuation
    restores an earlier word. -/
theorem no_raw_word_return (w u : Word) (hu : u ≠ []) : w ++ u ≠ w := by
  intro h
  have : (w ++ u).length = w.length := by rw [h]
  simp only [List.length_append] at this
  exact hu (List.eq_nil_of_length_eq_zero (by omega))

/-- **Theorem 2.4.** Status: Derived result. Nor an earlier matrix. The book
    argues by left multiplication and positive freeness; freeness is
    `Word.G_inj` in Elements I, so the matrix half reduces to the word half. -/
theorem no_raw_matrix_return (w u : Word) (hu : u ≠ []) : G (w ++ u) ≠ G w :=
  fun h => no_raw_word_return w u hu (G_inj h)

/-- Both halves, as the book states them. -/
theorem thm_2_4 (w u : Word) (hu : u ≠ []) : w ++ u ≠ w ∧ G (w ++ u) ≠ G w :=
  ⟨no_raw_word_return w u hu, no_raw_matrix_return w u hu⟩

/-- Stated on ancestry: a strict ancestor is never its own descendant. -/
theorem ancLt_irrefl (w : Word) : ¬ AncLt w w := fun h => h.2 rfl

/-! ## Corollary 2.5 — Every return is equality under a non-injective map -/

/-- **Corollary 2.5.** Status: Derived result. If a declared map reports a return
    — equality of a later reading with an earlier one across a nonempty
    continuation — then that map is not injective. The equality is a property of
    the map, never an erasure of the intervening history, which Theorem 2.4 shows
    is still there in the word and in the matrix. -/
theorem return_forces_noninjective {α : Type*} (κ : Word → α)
    {w u : Word} (hu : u ≠ []) (h : κ (w ++ u) = κ w) : ¬ Function.Injective κ :=
  fun hinj => no_raw_word_return w u hu (hinj h)

/-- The identity reading and the matrix reading admit no return, which is
    Theorem 2.4 restated as injectivity. -/
theorem wordClosure_injective : Function.Injective (id : Word → Word) := fun _ _ h => h

theorem matrixClosure_injective : Function.Injective G := fun _ _ h => G_inj h

/-- **Corollary 2.5 has an instance, and it is twelve letters long.** The escape
    clause is not empty: the closure residue of Elements I §8 is a declared
    reception map under which returns exist, and the shortest positive
    continuation producing one is `R¹²`. -/
theorem psi12_returns (w : Word) :
    psi12 (w ++ [true, true, true, true, true, true,
                 true, true, true, true, true, true]) = psi12 w := by
  have h12 : psi12 [true, true, true, true, true, true,
      true, true, true, true, true, true] = 0 := by decide +kernel
  rw [psi12_append, h12, add_zero]

theorem psi12_not_injective : ¬ Function.Injective psi12 :=
  return_forces_noninjective psi12 (by decide) (psi12_returns [])

/-! ## Separation Rule 2.6 — Distinct temporal readings

    Six readings of "how far apart" two events are: ledger separation
    `a_arch(n,k)`, continuation length `|v|`, directional imbalance `b(v)`,
    observer-relative geometry `Q`, endpoint contrast `T_end`, and the output of
    a declared reception map. "No one row is substituted for another without an
    explicit theorem."

    Three substitutions *do* have the explicit theorem, and it is Elements I's
    freeness. The other readings remain distinct unless a theorem connects them. -/

/-- **2.6, discharged pair.** `Q` determines the continuation length. The
    explicit theorem the rule asks for is `G_inj`. -/
theorem matrix_determines_length {u v : Word} (h : G u = G v) : len u = len v := by
  rw [G_inj h]

/-- **2.6, discharged pair.** `Q` determines the directional imbalance. -/
theorem matrix_determines_bal {u v : Word} (h : G u = G v) : bal u = bal v :=
  bal_of_G_eq h

/-- **2.6, discharged pair.** `Q` determines the received closure residue, for
    the reception map Elements I actually built. -/
theorem matrix_determines_psi12 {u v : Word} (h : G u = G v) : psi12 u = psi12 v := by
  rw [G_inj h]

/-- **2.6, non-substitution witness.** Continuation length does not determine imbalance:
    `RL` and `RR` have length `2` and imbalances `0` and `2`. -/
theorem length_not_bal :
    len [true, false] = len [true, true] ∧ bal [true, false] ≠ bal [true, true] := by
  refine ⟨rfl, ?_⟩; decide

/-- **2.6, non-substitution witness.** Imbalance does not determine continuation length:
    `R` and `RRL` both have imbalance `1`, at lengths `1` and `3`. -/
theorem bal_not_length :
    bal [true] = bal [true, true, false] ∧ len [true] ≠ len [true, true, false] := by
  refine ⟨by decide, ?_⟩; decide

/-- **2.6, non-substitution witness.** Length and imbalance together do not determine
    `Q`: `LR` and `RL` agree on both and are different matrices. Order is in the
    matrix and in neither count. -/
theorem length_bal_not_matrix :
    len [false, true] = len [true, false] ∧
      bal [false, true] = bal [true, false] ∧
      G [false, true] ≠ G [true, false] :=
  ⟨rfl, by decide, LR_ne_RL⟩

/-- **2.6, unpaired witness.** Ledger separation is not the continuation length.
    `continued_reading_age_not_continuation_length` below puts the two readings
    on the same record/read datum. -/
theorem age_not_length (k n : ℕ) (h : k ≤ n) :
    archiveAge ⟨⟨k, 0⟩, n, h⟩ = archiveAge ⟨⟨k, 0⟩, n, h⟩ ∧
      len [true] ≠ len [true, true] := ⟨rfl, by decide⟩

/-- **2.6, unpaired witness.** In the other direction, a continuation does not
    fix the ledger separation. `continued_reading_length_not_age` below makes the
    shared record explicit. -/
theorem length_not_age :
    archiveAge ⟨⟨1, 0⟩, 2, by decide⟩ ≠ archiveAge ⟨⟨1, 0⟩, 5, by decide⟩ := by
  decide

/-- **Separation Rule 2.6, exact coupling.** The directional imbalance of a
    continuation is bounded by its length. This is a relation between readings,
    not a substitution of either one for the other. -/
theorem continuation_bal_bounds (v : Word) :
    -(Word.len v : ℤ) ≤ bal v ∧ bal v ≤ Word.len v := by
  change -(v.length : ℤ) ≤ bal v ∧ bal v ≤ (v.length : ℤ)
  constructor
  · have h : -(bal v) ≤ (v.length : ℤ) := by
      calc
        -(bal v) = (v.count false : ℤ) - (v.count true : ℤ) := by
          unfold bal
          rw [Int.neg_sub]
        _ ≤ (v.count false : ℤ) := Int.sub_le_self _ (Int.natCast_nonneg _)
        _ ≤ (v.length : ℤ) := Int.ofNat_le.mpr List.count_le_length
    simpa using Int.neg_le_neg h
  · calc
      bal v = (v.count true : ℤ) - (v.count false : ℤ) := rfl
      _ ≤ (v.count true : ℤ) := Int.sub_le_self _ (Int.natCast_nonneg _)
      _ ≤ (v.length : ℤ) := Int.ofNat_le.mpr List.count_le_length

/-- **Separation Rule 2.6, exact coupling.** Length and directional imbalance
    have equal parity: their difference is twice the number of `L` letters. -/
theorem continuation_length_minus_bal_even (v : Word) :
    ∃ c : ℤ, (len v : ℤ) - bal v = 2 * c := by
  refine ⟨v.count false, ?_⟩
  have hcounts : ∀ w : Word, w.count true + w.count false = w.length := by
    intro w
    induction w with
    | nil => simp
    | cons b w ih => cases b <;> simp_all <;> omega
  unfold bal
  have h := hcounts v
  change (v.length : ℤ) - ((v.count true : ℤ) - (v.count false : ℤ)) = 2 * (v.count false : ℤ)
  omega

/-- **2.6, non-substitution witness.** For one fixed record/read event, archive
    age does not determine retained-continuation length. The two paired readings
    share exactly the same `Reading` component. -/
theorem continued_reading_age_not_continuation_length (k n : ℕ) (h : k ≤ n) :
    ∃ x y : ContinuedReading,
      x.reading = ⟨⟨k, 0⟩, n, h⟩ ∧
      y.reading = ⟨⟨k, 0⟩, n, h⟩ ∧
      archiveAge x.reading = archiveAge y.reading ∧
      len x.continuation ≠ len y.continuation := by
  refine ⟨⟨⟨⟨k, 0⟩, n, h⟩, [true]⟩,
    ⟨⟨⟨k, 0⟩, n, h⟩, [true, true]⟩, rfl, rfl, rfl, ?_⟩
  change 1 ≠ 2
  decide

/-- **2.6, non-substitution witness.** For one fixed archived record and one
    retained continuation, continuation length does not determine archive age. -/
theorem continued_reading_length_not_age :
    ∃ x y : ContinuedReading,
      x.reading.entry = y.reading.entry ∧
      x.continuation = [true] ∧
      y.continuation = [true] ∧
      len x.continuation = len y.continuation ∧
      archiveAge x.reading ≠ archiveAge y.reading := by
  refine ⟨⟨⟨⟨1, 0⟩, 2, by decide⟩, [true]⟩,
    ⟨⟨⟨1, 0⟩, 5, by decide⟩, [true]⟩, rfl, rfl, rfl, rfl, by decide⟩

/-- **2.6, non-substitution witness.** The received closure residue does not determine
    `Q`: `R¹²` and `ε` share the residue `0` and differ as matrices, by 2.5's
    instance. Reception is strictly coarser than geometry. -/
theorem psi12_not_matrix :
    psi12 [true, true, true, true, true, true,
           true, true, true, true, true, true] = psi12 ([] : Word) ∧
      G [true, true, true, true, true, true,
         true, true, true, true, true, true] ≠ G ([] : Word) := by
  refine ⟨by simpa using psi12_returns [], ?_⟩
  exact no_raw_matrix_return [] _ (by decide)

/-- **Separation Rule 2.6, assembled.** Of the readings that are functions of the
    continuation word, `Q` is strictly finest: it determines length, imbalance
    and residue, and none of those three determines it. Ledger separation has
    the two paired non-substitution witnesses above, while length and imbalance
    retain their stated exact couplings. The rule's "without an explicit theorem"
    is therefore a live clause with three discharges already on the books, not a
    blanket prohibition. -/
theorem sep_2_6_summary :
    (∀ u v : Word, G u = G v → len u = len v ∧ bal u = bal v ∧ psi12 u = psi12 v) ∧
      (∃ u v : Word, len u = len v ∧ bal u = bal v ∧ G u ≠ G v) :=
  ⟨fun _ _ h => ⟨matrix_determines_length h, matrix_determines_bal h,
      matrix_determines_psi12 h⟩,
   ⟨[false, true], [true, false], rfl, by decide, LR_ne_RL⟩⟩

end Two
end RatioSpace
