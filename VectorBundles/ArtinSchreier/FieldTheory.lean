module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.Cycle.Type

@[expose] public section

open IntermediateField

lemma cyclic_char_p_as_artin_schreier (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (hp: Nat.Prime p) (hrank: Module.finrank F K = p)
  (hsep: IsGalois F K) (hchar: ringChar F = p) : ∃ (a : F), ∃ (x : K),
  minpoly F x = Polynomial.X ^ p - Polynomial.X - Polynomial.C a := by
  sorry

lemma nonsquare_in_quadratic_extension (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (hrank: Module.finrank F K = 2) (hchar: ringChar F ≠ 2) :
  ∃ a : F, ¬ IsSquare a := by

  have _ : ringChar F = ringChar K := by
    exact Algebra.ringChar_eq F K
  have _ : CharP F (ringChar K) := by
    (expose_names; exact ringChar.of_eq h)
  have prim : (primitiveRoots (Module.finrank F K) F).Nonempty := by
    unfold primitiveRoots
    refine Finset.nonempty_def.mpr ?_
    use -1
    simp_all
    refine IsPrimitiveRoot.neg_one (ringChar K) ?_
    simp_all
  have _ : Algebra.IsQuadraticExtension F K := by
    exact { toFree := Module.free_of_finite_type_torsion_free', finrank_eq_two' := hrank }
  have _ : Algebra.IsSeparable F K := by
    let d := Field.finInsepDegree F K
    let e := Field.finSepDegree F K
    let q := ringExpChar F
    have hd : d ∣ 2 := by
      have h_de : Field.finSepDegree F K * Field.finInsepDegree F K = Module.finrank F K := by
        exact Field.finSepDegree_mul_finInsepDegree F K
      have _ : e * d = Module.finrank F K := by
        subst d e
        apply h_de
      have _ : e * d = 2 := by
        simp_all
      (expose_names; exact dvd_of_mul_left_eq e h_4)
    have hf : ∃ f : ℕ, d = q^f := by
      apply finInsepDegree_eq_pow
    obtain ⟨f, hf⟩ := hf
    by_cases d = 1
    · (expose_names; exact (isSeparable_iff_finInsepDegree_eq_one F K).mpr h_3)
    · have h_f : d = 2 := by
        have _ : Nat.Prime 2 := by
          exact Nat.prime_two
        have _ : Nat.Prime 2 → (d ∣ 2 ↔ d = 1 ∨ d = 2) :=
          Nat.dvd_prime
        simp_all
      have h_chars : ∀ (p q : ℕ) [hp : CharP F p] [hq : ExpChar F q], p = q ↔ Nat.Prime p :=
        char_eq_expChar_iff F
      have _ : CharP F (ringChar F) := by
        exact ringChar.charP F
      specialize h_chars (ringChar F) q
      have h_pq : Nat.Prime (ringChar F) ∧ Nat.Prime q ∧ (ringChar F) = q := by
        have h_chars2 : ∀ (p q : ℕ) [CharP F p] [ExpChar F q], q = 1 ↔ p = 0 :=
          expChar_one_iff_char_zero F
        specialize h_chars2 (ringChar F) q
        have h_chars3 : ∀ (p : ℕ) [hc : CharP F p], Nat.Prime p ∨ p = 0 :=
          CharP.char_is_prime_or_zero F
        specialize h_chars3 (ringChar F)
        simp_all
      obtain ⟨h_pq1, h_pq2, h_pq3⟩ := h_pq
      exfalso
      have _ : f ≥ 1 := by
        by_contra
        push Not at this
        have _ : f = 0 := by
          simp_all
        have _ : q ^ f = 1 := by
          (expose_names;
            exact pow_eq_one_iff_modEq.mpr (congrFun (congrArg HMod.hMod h_5) (orderOf q)))
        simp_all
      have h_q2 : q ∣ 2 := by
        have _ : f ≥ 1 → q^1 ∣ q^f := by
          (expose_names; exact fun a => Nat.pow_dvd_pow q h_5)
        grind
      have _ : q = 2 := by
        have _ : Nat.Prime 2 := by
          exact Nat.prime_two
        have _ : Nat.Prime 2 → (q ∣ 2 ↔ q = 1 ∨ q = 2) :=
          Nat.dvd_prime
        have _ : q ≠ 1 := by
          by_contra
          have _ : q ^ f = 1 := by
            refine Nat.pow_eq_one.mpr ?_
            left
            exact this
          grind
        grind
      grind
  have _ : IsGalois F K := by
    (expose_names;
      exact { to_isSeparable := h_3, to_normal := Algebra.IsQuadraticExtension.normal F K })
  have _ : IsCyclic Gal(K/F) := by
    (expose_names; refine Algebra.IsQuadraticExtension.isCyclic F K)
  have hb : ∃ (b : K), b ^ Module.finrank F K ∈ Set.range (algebraMap F K) ∧ F⟮b⟯ = (⊤: IntermediateField F K) :=
    exists_root_adjoin_eq_top_of_isCyclic F K prim
  obtain ⟨b, hb1, hb2⟩ := hb
  have ha : ∃ (a : F), b ^ 2 = (algebraMap F K) a := by
    simp_all
    obtain ⟨a, hb1⟩ := hb1
    use a
    symm
    exact hb1
  obtain ⟨a, ha⟩ := ha
  use a
  by_contra
  unfold IsSquare at this
  obtain ⟨c, this⟩ := this
  have hb3 : (algebraMap F K) c = b ∨ (algebraMap F K) (-c) = b := by
    grind
  have _ : b ∈ (algebraMap F K).range := by
    refine RingHom.mem_range.mpr ?_
    cases hb3
    · use c
    · use -c
  have _ : F⟮b⟯ = (⊥: IntermediateField F K) := by
    (expose_names; exact adjoin_simple_eq_bot_iff.mpr h_6)
  have _ : Module.finrank F K = 1 := by
    have _ : (⊥: IntermediateField F K) = (⊤: IntermediateField F K) := by
      simp_all
    (expose_names; exact bot_eq_top_iff_finrank_eq_one.mp h_8)
  simp_all

lemma trivial_absolute_galois_group (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [Algebra.IsSeparable F K] [IsAlgClosure F K]
  [FiniteDimensional F K] (h : Nat.card Gal(K/F) = 1) : IsAlgClosed F := by
  have _ : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_3, to_normal := IsAlgClosure.normal F K })
  have _ : Nat.card Gal(K/F) = Module.finrank F K := by
    apply IsGaloisGroup.card_eq_finrank
  have _ : Module.finrank F K = 1 := by
    simp_all
  have _ : IsAlgClosed K := by
    exact IsAlgClosure.isAlgClosed F
  have h_range: ∀ (b : K), b ∈ (algebraMap F K).range := by
    intro b
    let pol := minpoly F b
    refine minpoly.natDegree_eq_one_iff.mp ?_
    have _ : (minpoly F b).natDegree ≤ Module.finrank F K := by
      apply minpoly.natDegree_le
    have _ : pol.natDegree ≤ 1 := by
      grind
    have _ : Irreducible pol := by
      refine minpoly.irreducible ?_
      exact Algebra.IsIntegral.isIntegral b
    have _ : Irreducible pol → 0 < Polynomial.natDegree pol :=
      Irreducible.natDegree_pos
    have _ : pol.natDegree ≠ 0 := by
      (expose_names; exact Nat.ne_zero_iff_zero_lt.mpr (h_8 h_7))
    grind
  refine IsAlgClosed.of_exists_root F ?_
  intro p h1 h2
  have hb: ∃ (b : K), Polynomial.aeval b p = 0 := by
    let p_K := p.map (algebraMap F K)
    have _ : p_K.Splits := by
      exact IsAlgClosed.splits p_K
    refine IsAlgClosed.exists_aeval_eq_zero K p ?_
    have _ : Irreducible p → 0 < Polynomial.degree p :=
      Irreducible.degree_pos
    simp_all
    (expose_names; exact ne_of_gt h_5)
  obtain ⟨b, hb⟩ := hb
  specialize h_range b
  have ha : ∃ (a : F), (algebraMap F K) a = b := by
    exact Set.mem_range.mp h_range
  obtain ⟨a, ha⟩ := ha
  use a
  have _ : (algebraMap F K) (Polynomial.eval a p) = Polynomial.eval ((algebraMap F K) a) (p.map (algebraMap F K)) := by
    exact Eq.symm (Polynomial.eval_map_apply (algebraMap F K) a)
  simp_all
