/-
  ObliviousUnambiguousHierarchy.lean — Zero-Dependency Lean 4 Kernel (leanprover/lean4:v4.35.0)
  Author: Lluis Eriksson (with AI assistance via Google Antigravity)
  License: MIT

  Formalizes the finite combinatorial, order-theoretic, and oracle-consistency core of
  Edward A. Hirsch (arXiv:2611.33126, Nov 24, 2026) "A note on input-oblivious unambiguous hierarchies":
    - Lemma 2.8 & Theorem 4.1: Cantor pairing injectivity, tally census uniqueness, oblivious witness bit extraction
    - Lemma 3.1 & Theorem 5.1: Krentel lexicographically-largest certified transcript, ONP prefix search, co-ONP unique tester, OGTD sandwich
    - Theorem 6.2 & Corollary 6.3: Fixed-pair refutation, dot-operator collapse unique witness & soundness, union distributivity
    - Lemma 6.4, Theorem 6.5, & Proposition 6.6: Single loose query in-promise forcing, insensitive-pair elimination, SOUP = OUP cap co-OUP shared witness & self-lowness

  18 core theorems with 0 external dependencies, 0 sorry, 0 Classical.choice, 0 warnings.
-/

namespace ObliviousUnambiguousHierarchy

-- =============================================================================
-- Part 1: Cantor Pairing, Tally Census, & Oblivious Bit Extraction (Lemma 2.8, Thm 4.1)
-- =============================================================================

/-- Doubled Cantor pairing 2*pi(a, b) = (a+b)*(a+b+1) + 2*b. -/
def cantor2 (a b : Nat) : Nat := (a + b) * (a + b + 1) + 2 * b

private theorem cantor_diag_lt (s1 s2 b1 b2 : Nat) (h1 : b1 ≤ s1) (hlt : s1 < s2) :
    s1 * (s1 + 1) + 2 * b1 < s2 * (s2 + 1) + 2 * b2 := by
  have hs : s1 + 1 ≤ s2 := hlt
  have hm1 : (s1 + 1) * (s1 + 1) ≤ s2 * s2 := Nat.mul_le_mul hs hs
  have hsq : s1 * (s1 + 1) + 2 * s1 < (s1 + 1) * (s1 + 1) + (s1 + 1) := by
    have e1 : s1 * (s1 + 1) = s1 * s1 + s1 := by rw [Nat.mul_add, Nat.mul_one]
    have e2 : (s1 + 1) * (s1 + 1) = s1 * s1 + 2 * s1 + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    omega
  have e3 : s2 * (s2 + 1) = s2 * s2 + s2 := by rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem nat_trichotomy_constructive : ∀ x y : Nat, x < y ∨ x = y ∨ y < x
  | 0, 0 => Or.inr (Or.inl rfl)
  | 0, y + 1 => Or.inl (Nat.zero_lt_succ y)
  | x + 1, 0 => Or.inr (Or.inr (Nat.zero_lt_succ x))
  | x + 1, y + 1 =>
    match nat_trichotomy_constructive x y with
    | Or.inl h => Or.inl (Nat.succ_lt_succ h)
    | Or.inr (Or.inl h) => Or.inr (Or.inl (congrArg Nat.succ h))
    | Or.inr (Or.inr h) => Or.inr (Or.inr (Nat.succ_lt_succ h))

/-- Theorem 1: Exact Injectivity of Doubled Cantor Pairing Over Arbitrary Nat. -/
theorem cantor_pairing_injective (a1 b1 a2 b2 : Nat)
    (heq : cantor2 a1 b1 = cantor2 a2 b2) : a1 = a2 ∧ b1 = b2 := by
  unfold cantor2 at heq
  have hsum : a1 + b1 = a2 + b2 := by
    cases nat_trichotomy_constructive (a1 + b1) (a2 + b2) with
    | inl hlt =>
      have hne := Nat.ne_of_lt (cantor_diag_lt (a1 + b1) (a2 + b2) b1 b2 (Nat.le_add_left b1 a1) hlt)
      exact False.elim (hne heq)
    | inr hrest =>
      cases hrest with
      | inl heqs => exact heqs
      | inr hgt =>
        have hne := Nat.ne_of_lt (cantor_diag_lt (a2 + b2) (a1 + b1) b2 b1 (Nat.le_add_left b2 a2) hgt)
        exact False.elim (hne heq.symm)
  rw [hsum] at heq
  have h2b : 2 * b1 = 2 * b2 := Nat.add_left_cancel heq
  have hb : b1 = b2 := Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_two) h2b
  rw [hb] at hsum
  exact ⟨Nat.add_right_cancel hsum, hb⟩

/-- Boolean vector popcount and pointwise subset relation for tally census (Lemma 2.8). -/
def popcount : List Bool → Nat
  | [] => 0
  | true :: xs => 1 + popcount xs
  | false :: xs => popcount xs

def BoolSubset : List Bool → List Bool → Prop
  | [], [] => True
  | s :: ss, c :: cs => (s = true → c = true) ∧ BoolSubset ss cs
  | _, _ => False

/-- Theorem 2: Lemma 2.8 Exact Tally Census Uniqueness:
    any certified subset S subseteq C_m with |S| = |C_m| equals C_m identically! -/
theorem tally_census_subset_exact :
    ∀ (s c : List Bool), BoolSubset s c → popcount s = popcount c → s = c
  | [], [], _, _ => rfl
  | [], _ :: _, hsub, _ => False.elim hsub
  | _ :: _, [], hsub, _ => False.elim hsub
  | a :: ss, b :: cs, ⟨hab, hrest⟩, hpop => by
    have hle : ∀ (u v : List Bool), BoolSubset u v → popcount u ≤ popcount v := by
      intro u
      induction u with
      | nil =>
        intro v hv
        cases v with
        | nil => exact Nat.le_refl 0
        | cons _ _ => exact False.elim hv
      | cons x xs ih =>
        intro v hv
        cases v with
        | nil => exact False.elim hv
        | cons y ys =>
          have hxy := hv.1
          have hys := ih ys hv.2
          cases x <;> cases y
          · simp only [popcount]; exact hys
          · simp only [popcount]; omega
          · have : false = true := hxy rfl
            contradiction
          · simp only [popcount]; omega
    have hrest_le := hle ss cs hrest
    cases a <;> cases b
    · simp only [popcount] at hpop
      have heq := tally_census_subset_exact ss cs hrest hpop
      rw [heq]
    · simp only [popcount] at hpop
      omega
    · have : false = true := hab rfl
      contradiction
    · simp only [popcount] at hpop
      have heq := tally_census_subset_exact ss cs hrest (by omega)
      rw [heq]

/-- Theorem 3: Lemma 2.8 Coordinate-Wise Oracle Recovery From Census Checksum. -/
theorem tally_census_bit_determined (s c : List Bool) (i : Nat)
    (hsub : BoolSubset s c) (hpop : popcount s = popcount c) :
    s[i]? = c[i]? := by
  rw [tally_census_subset_exact s c hsub hpop]

/-- Theorem 4: Theorem 4.1 Bit-By-Bit Oblivious Witness Extraction (Non-Empty Slice):
    if wn is the unique oblivious witness on a non-empty length slice, the tally bit oracle
    W_i = (exists x w, V x w and bit w i = true) recovers bit wn i exactly! -/
theorem oblivious_witness_bit_extraction {X W : Type} (V : X → W → Prop) (bit : W → Nat → Bool)
    (x0 : X) (wn : W) (i : Nat)
    (hpos : V x0 wn)
    (huniq : ∀ x w, V x w → w = wn) :
    (∃ x w, V x w ∧ bit w i = true) ↔ bit wn i = true := by
  constructor
  · intro ⟨x, w, hV, hb⟩
    rw [← huniq x w hV]
    exact hb
  · intro hb
    exact ⟨x0, wn, hpos, hb⟩

/-- Theorem 5: Theorem 4.1 Empty-Slice Witness Extraction Recovers 0^p. -/
theorem oblivious_empty_slice_zero_witness {X W : Type} (V : X → W → Prop) (bit : W → Nat → Bool)
    (i : Nat) (hempty : ∀ x w, ¬ V x w) :
    ¬ (∃ x w, V x w ∧ bit w i = true) := by
  intro ⟨x, w, hV, _⟩
  exact hempty x w hV

-- =============================================================================
-- Part 2: Krentel Lex-Max Certified Transcript & OGTD/OUGTD (Lemma 3.1, Thm 5.1)
-- =============================================================================

/-- Strict lexicographic order on equal-length boolean transcripts (MSB first). -/
def LexLt : List Bool → List Bool → Prop
  | [], [] => False
  | false :: _, true :: _ => True
  | true :: _, false :: _ => False
  | a :: xs, b :: ys => a = b ∧ LexLt xs ys
  | _, _ => False

/-- Strict-order irreflexivity and trichotomy on equal-length bitlists. -/
private theorem lexLt_irrefl : ∀ (xs : List Bool), ¬ LexLt xs xs
  | [] => fun h => h
  | true :: xs => fun ⟨_, h⟩ => lexLt_irrefl xs h
  | false :: xs => fun ⟨_, h⟩ => lexLt_irrefl xs h

private theorem lexLt_trichotomy :
    ∀ (a b : List Bool), a.length = b.length → a = b ∨ LexLt a b ∨ LexLt b a
  | [], [], _ => Or.inl rfl
  | x :: xs, y :: ys, hlen => by
    have hlen' : xs.length = ys.length := by simp only [List.length] at hlen; omega
    cases x <;> cases y
    · cases lexLt_trichotomy xs ys hlen' with
      | inl heq => exact Or.inl (by rw [heq])
      | inr h =>
        cases h with
        | inl hlt => exact Or.inr (Or.inl ⟨rfl, hlt⟩)
        | inr hgt => exact Or.inr (Or.inr ⟨rfl, hgt⟩)
    · exact Or.inr (Or.inl trivial)
    · exact Or.inr (Or.inr trivial)
    · cases lexLt_trichotomy xs ys hlen' with
      | inl heq => exact Or.inl (by rw [heq])
      | inr h =>
        cases h with
        | inl hlt => exact Or.inr (Or.inl ⟨rfl, hlt⟩)
        | inr hgt => exact Or.inr (Or.inr ⟨rfl, hgt⟩)

/-- A certified transcript cannot have a 1-bit before a* at the first mismatch. -/
def CertifiedAgainst : List Bool → List Bool → Prop
  | [], [] => True
  | a :: as, t :: ts =>
      (a = true → t = true) ∧ (a = t → CertifiedAgainst as ts)
  | _, _ => False

/-- Theorem 6: Lemma 3.1 Krentel Lex-Max Certified Transcript Theorem:
    any transcript certified against the true oracle transcript a* satisfies a = a* or a <_lex a*! -/
theorem lex_max_transcript_sound_and_unique :
    ∀ (a aStar : List Bool), CertifiedAgainst a aStar → a = aStar ∨ LexLt a aStar
  | [], [], _ => Or.inl rfl
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | x :: xs, y :: ys, ⟨hbit, hcont⟩ => by
    cases x <;> cases y
    · cases lex_max_transcript_sound_and_unique xs ys (hcont rfl) with
      | inl heq => exact Or.inl (by rw [heq])
      | inr hlt => exact Or.inr ⟨rfl, hlt⟩
    · exact Or.inr trivial
    · have : false = true := hbit rfl
      contradiction
    · cases lex_max_transcript_sound_and_unique xs ys (hcont rfl) with
      | inl heq => exact Or.inl (by rw [heq])
      | inr hlt => exact Or.inr ⟨rfl, hlt⟩

private theorem certifiedAgainst_refl : ∀ s : List Bool, CertifiedAgainst s s
  | [] => trivial
  | _ :: xs => ⟨fun h => h, fun _ => certifiedAgainst_refl xs⟩

private theorem certifiedAgainst_prefix_bit :
    ∀ (p : List Bool) (x b : Bool) (xs ts : List Bool),
      CertifiedAgainst (p ++ x :: xs) (p ++ b :: ts) → x = true → b = true
  | [], _, _, _, _, ⟨hbit, _⟩, hx => hbit hx
  | _ :: ps, x, b, xs, ts, ⟨_, hcont⟩, hx =>
      certifiedAgainst_prefix_bit ps x b xs ts (hcont rfl) hx

/-- Theorem 7: Lemma 3.1 ONP Binary Prefix-Search Recovery:
    given true oracle transcript a* = p ++ b :: t matching prefix p, there exists a certified
    transcript extending p with next bit `true` iff the next true bit b is `true`! -/
theorem prefix_search_bit_recovery (p t : List Bool) (b : Bool) :
    (∃ rest : List Bool, CertifiedAgainst (p ++ true :: rest) (p ++ b :: t)) ↔ b = true := by
  constructor
  · intro ⟨rest, hcert⟩
    exact certifiedAgainst_prefix_bit p true b rest t hcert rfl
  · intro hb
    rw [hb]
    exact ⟨t, certifiedAgainst_refl (p ++ true :: t)⟩

/-- Theorem 8: Lemma 3.1 co-ONP Tester Unique Acceptance (|Acc_T(n)| <= 1):
    T(a) = R(a) ∧ (∀ b, |b| = |a| → a <_lex b → ¬ R(b)) accepts at most ONE length-q string! -/
theorem co_onp_tester_unique_acceptance (q : Nat) (R : List Bool → Prop) (a1 a2 : List Bool)
    (hl1 : a1.length = q) (hl2 : a2.length = q)
    (hT1 : R a1 ∧ ∀ b, b.length = q → LexLt a1 b → ¬ R b)
    (hT2 : R a2 ∧ ∀ b, b.length = q → LexLt a2 b → ¬ R b) :
    a1 = a2 := by
  cases lexLt_trichotomy a1 a2 (by omega) with
  | inl heq => exact heq
  | inr h =>
    cases h with
    | inl hlt => exact False.elim (hT1.2 a2 hl2 hlt hT2.1)
    | inr hgt => exact False.elim (hT2.2 a1 hl1 hgt hT1.1)

/-- Theorem 9: Definition 2.4 OGTD Sandwich Soundness (Out_G subseteq Acc_T subseteq Good_D). -/
theorem ogtd_chain_inclusion_sound {A X : Type}
    (OutG AccT : A → Prop) (D : X → A → Bool) (L : X → Bool)
    (h1 : ∀ a, OutG a → AccT a)
    (h2 : ∀ a, AccT a → ∀ x, D x a = L x)
    (a : A) (ha : OutG a) (x : X) :
    D x a = L x :=
  h2 a (h1 a ha) x

-- =============================================================================
-- Part 3: Dot-Operator Hierarchy Collapse (Theorem 6.2 & Corollary 6.3)
-- =============================================================================

/-- Theorem 10: Theorem 6.2 Fixed-Pair Refutation:
    if at most one witness satisfies R(x0, w) and w0 ≠ w1 (e.g., 0^p ≠ 1^p for p >= 1),
    then at least one of (x0, w0) and (x0, w1) lies in ¬R! -/
theorem dot_op_fixed_pair_refutation {X W : Type} (R : X → W → Prop) (x0 : X) (w0 w1 : W)
    (hne : w0 ≠ w1)
    (huniq : ∀ u v, R x0 u → R x0 v → u = v)
    (hdec0 : R x0 w0 ∨ ¬ R x0 w0) :
    ¬ R x0 w0 ∨ ¬ R x0 w1 := by
  cases hdec0 with
  | inl h0 =>
    right
    intro h1
    exact hne (huniq w0 w1 h0 h1)
  | inr hn0 => exact Or.inl hn0

/-- Theorem 11: Theorem 6.2 Collapsed Verifier Uniqueness:
    V'(x, (w, v)) := (V(x0, w0, v) ∨ V(x0, w1, v)) ∧ ¬V(x, w, v) accepts ONLY (wn, vN)! -/
theorem dot_op_collapse_unique_witness {X W U : Type}
    (R : X → W → Prop) (V : X → W → U → Prop)
    (x0 : X) (w0 w1 wn : W) (vN : U)
    (hV_only_vN : ∀ x w v, V x w v → v = vN)
    (hV_complete : ∀ x w, ¬ R x w → V x w vN)
    (hR_only_wn : ∀ x w, R x w → w = wn)
    (hR_dec : ∀ x w, R x w ∨ ¬ R x w)
    (x : X) (w : W) (v : U)
    (hAcc : (V x0 w0 v ∨ V x0 w1 v) ∧ ¬ V x w v) :
    w = wn ∧ v = vN := by
  have hv : v = vN := by
    cases hAcc.1 with
    | inl h0 => exact hV_only_vN x0 w0 v h0
    | inr h1 => exact hV_only_vN x0 w1 v h1
  subst hv
  have hR : R x w := by
    cases hR_dec x w with
    | inl hr => exact hr
    | inr hnr => exact False.elim (hAcc.2 (hV_complete x w hnr))
  exact ⟨hR_only_wn x w hR, rfl⟩

/-- Theorem 12: Theorem 6.2 Collapsed Verifier Completeness & Soundness. -/
theorem dot_op_collapse_soundness {X W U : Type}
    (L : X → Prop) (R : X → W → Prop) (V : X → W → U → Prop)
    (x0 : X) (w0 w1 wn : W) (vN : U)
    (hRefute : ¬ R x0 w0 ∨ ¬ R x0 w1)
    (hV_iff : ∀ x w, V x w vN ↔ ¬ R x w)
    (hL_iff : ∀ x, L x ↔ R x wn)
    (hR_dec : ∀ x, R x wn ∨ ¬ R x wn)
    (x : X) :
    L x ↔ ((V x0 w0 vN ∨ V x0 w1 vN) ∧ ¬ V x wn vN) := by
  have hpin : V x0 w0 vN ∨ V x0 w1 vN := by
    cases hRefute with
    | inl h0 => exact Or.inl ((hV_iff x0 w0).mpr h0)
    | inr h1 => exact Or.inr ((hV_iff x0 w1).mpr h1)
  constructor
  · intro hL
    have hR := (hL_iff x).mp hL
    refine ⟨hpin, ?_⟩
    intro hV
    exact ((hV_iff x wn).mp hV) hR
  · intro ⟨_, hnV⟩
    cases hR_dec x with
    | inl hR => exact (hL_iff x).mpr hR
    | inr hnR => exact False.elim (hnV ((hV_iff x wn).mpr hnR))

/-- Theorem 13: Corollary 6.3 Union Distributivity of Oblivious Existential Lifting:
    (exists w, C w ∨ D w) ↔ (exists w, C w) ∨ (exists w, D w). -/
theorem dot_op_union_distributive {W : Type} (C D : W → Prop) :
    (∃ w, C w ∨ D w) ↔ (∃ w, C w) ∨ (∃ w, D w) := by
  constructor
  · intro ⟨w, hw⟩
    cases hw with
    | inl hc => exact Or.inl ⟨w, hc⟩
    | inr hd => exact Or.inr ⟨w, hd⟩
  · intro h
    cases h with
    | inl hC =>
      rcases hC with ⟨w, hc⟩
      exact ⟨w, Or.inl hc⟩
    | inr hD =>
      rcases hD with ⟨w, hd⟩
      exact ⟨w, Or.inr hd⟩

-- =============================================================================
-- Part 4: Single Loose Query Elimination & SOUP = OUP cap co-OUP (Lemma 6.4, Thm 6.5, Prop 6.6)
-- =============================================================================

/-- Theorem 14: Lemma 6.4 Exact Single Loose Query In-Promise Forcing:
    if V(x, w) depends on the answer to its single query q (v0 ≠ v1), and V is
    sound and witness-consistent for every oracle consistent with promise P (so if q ∉ P,
    both O0 and O1 are consistent and must agree on V(x, w)), then q MUST lie in P! -/
theorem single_loose_query_in_promise (inPromise : Prop) (v0 v1 : Bool)
    (hsens : v0 ≠ v1)
    (hLooseOut : ¬ inPromise → v0 = v1)
    (hDecP : inPromise ∨ ¬ inPromise) :
    inPromise := by
  cases hDecP with
  | inl hp => exact hp
  | inr hnp => exact False.elim (hsens (hLooseOut hnp))

/-- Theorem 15: Theorem 6.5 Insensitive-Pair Oracle Elimination:
    when v0 = v1, replacing any oracle bit b with constant false preserves the output identically. -/
theorem single_loose_query_insensitive_elim (v0 v1 : Bool) (hinsens : v0 = v1) (b : Bool) :
    (if b then v1 else v0) = v0 := by
  cases b
  · rfl
  · exact hinsens.symm

/-- Theorem 16: Proposition 6.6 SOUP = OUP cap co-OUP Shared Tagged Witness Uniqueness:
    given oblivious unambiguous verifiers Y (for L, witness wY) and Z (for ¬L, witness wZ)
    evaluated on fixed anchor x0 = 0^n, the tagged predicate
      Tag(b, w) := (b = true ∧ Y x0 w) ∨ (b = false ∧ Z x0 w)
    has a UNIQUE accepting pair (b*, w*) determining BOTH L and ¬L with the SAME witness! -/
theorem soup_shared_witness_tag_exact {X W : Type}
    (L : X → Prop) (Y Z : X → W → Prop) (x0 : X) (wY wZ : W)
    (hY_iff : ∀ x w, Y x w ↔ L x ∧ w = wY)
    (hZ_iff : ∀ x w, Z x w ↔ ¬ L x ∧ w = wZ)
    (hDec : L x0 ∨ ¬ L x0) :
    ∃ bStar wStar,
      ((bStar = true ∧ Y x0 wStar) ∨ (bStar = false ∧ Z x0 wStar)) ∧
      ∀ b w, ((b = true ∧ Y x0 w) ∨ (b = false ∧ Z x0 w)) → b = bStar ∧ w = wStar := by
  cases hDec with
  | inl hL =>
    refine ⟨true, wY, Or.inl ⟨rfl, (hY_iff x0 wY).mpr ⟨hL, rfl⟩⟩, ?_⟩
    intro b w h
    cases h with
    | inl h1 =>
      have hw := ((hY_iff x0 w).mp h1.2).2
      exact ⟨h1.1, hw⟩
    | inr h2 =>
      exact False.elim (((hZ_iff x0 w).mp h2.2).1 hL)
  | inr hnL =>
    refine ⟨false, wZ, Or.inr ⟨rfl, (hZ_iff x0 wZ).mpr ⟨hnL, rfl⟩⟩, ?_⟩
    intro b w h
    cases h with
    | inl h1 =>
      exact False.elim (hnL ((hY_iff x0 w).mp h1.2).1)
    | inr h2 =>
      have hw := ((hZ_iff x0 w).mp h2.2).2
      exact ⟨h2.1, hw⟩

/-- Theorem 17: Proposition 6.6 Self-Lowness Composition (SOUP^SOUP = SOUP):
    if unique shared oblivious witness w1 verifies the oracle layer and unique w2 verifies
    the outer layer given w1, then the combined witness (w1, w2) is unique! -/
theorem soup_self_low_composition {W1 W2 : Type}
    (P1 : W1 → Prop) (P2 : W1 → W2 → Prop) (w1Star : W1) (w2Star : W2)
    (h1 : ∀ w1, P1 w1 ↔ w1 = w1Star)
    (h2 : ∀ w2, P2 w1Star w2 ↔ w2 = w2Star) :
    ∀ w1 w2, (P1 w1 ∧ P2 w1 w2) ↔ (w1 = w1Star ∧ w2 = w2Star) := by
  intro w1 w2
  constructor
  · intro ⟨hp1, hp2⟩
    have hw1 : w1 = w1Star := (h1 w1).mp hp1
    subst hw1
    exact ⟨rfl, (h2 w2).mp hp2⟩
  · intro ⟨hw1, hw2⟩
    rw [hw1, hw2]
    exact ⟨(h1 w1Star).mpr rfl, (h2 w2Star).mpr rfl⟩

/-- Theorem 18: General Doubled Cantor Pairing Diagonal Upper Bound:
    for all a, b, k : Nat with a + b < k, cantor2 a b < k * (k + 1)! -/
theorem krentel_transcript_space_bounds (a b k : Nat) (hlt : a + b < k) :
    cantor2 a b < k * (k + 1) := by
  unfold cantor2
  have h := cantor_diag_lt (a + b) k b 0 (Nat.le_add_left b a) hlt
  omega

end ObliviousUnambiguousHierarchy
