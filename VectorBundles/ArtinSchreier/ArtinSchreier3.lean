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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField

lemma finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (h: Module.finrank F K = p)
  (hsep: IsGalois F K): ¬ ringChar F = p := by
  by_contra
  have ha :  ∃ (a : F), ∃ (x : K),
    minpoly F x = Polynomial.X ^ p - Polynomial.X - Polynomial.C a := by
    apply cyclic_char_p_as_artin_schreier F K p hp h hsep this
  obtain ⟨a, x, ha⟩ := ha
  let pol := Polynomial.X ^ p - Polynomial.X - Polynomial.C (x ^ (p-1) * ((algebraMap F K) a))
  have _ : pol.degree = p := by
    sorry
  have _ : ∃ y : K, Polynomial.aeval y pol = 0 := by
    have _ : IsAlgClosed K := by
      exact IsAlgClosure.isAlgClosed F
    refine IsAlgClosed.exists_aeval_eq_zero K pol ?_
    simp_all
    exact Nat.Prime.ne_zero hp
  sorry

lemma finite_algebraic_closure_cyclic_quadratic (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (hrank: Module.finrank F K = p)
  (hgal: IsGalois F K): p = 2 := by
  have h_char : ¬ ringChar F = p :=
    finite_algebraic_closure_cyclic_prime F K p hp hrank hgal
  have hK : (primitiveRoots (Module.finrank F K) F).Nonempty := by
    let cyclo := Polynomial.cyclotomic p F
    have _ : cyclo.degree = p.totient := by
      apply Polynomial.degree_cyclotomic
    have _ : p.totient = p - 1 := by
      exact Nat.totient_prime hp
    have h_cycloroot : ∃ y : K, Polynomial.aeval y cyclo = 0 := by
      have _ : IsAlgClosed K := by
        exact IsAlgClosure.isAlgClosed F
      refine IsAlgClosed.exists_aeval_eq_zero K cyclo ?_
      simp_all
      refine Nat.sub_ne_zero_of_lt ?_
      exact Nat.Prime.one_lt hp
    obtain ⟨y, h_cycloroot⟩ := h_cycloroot
    let f := minpoly F y
    have _ : f.natDegree ∣ Module.finrank F K := by
      refine minpoly.degree_dvd ?_
      exact Algebra.IsIntegral.isIntegral y
    have _ : f ∣ cyclo := by
      exact minpoly.dvd_iff.mpr h_cycloroot
    have _ : f.natDegree ≤ cyclo.natDegree := by
      (expose_names; refine Polynomial.natDegree_le_of_dvd h_3 ?_)
      exact Polynomial.cyclotomic_ne_zero p F
    have _ : f.natDegree = 1 := by
      have _ : f.natDegree ∣ p := by
        simp_all
      have hfd : f.natDegree = 1 ∨ f.natDegree = p := by
        (expose_names; exact Nat.Prime.eq_one_or_self_of_dvd hp f.natDegree h_5)
      cases hfd
      · simp_all
      · exfalso
        simp_all
        have _ : cyclo.natDegree = p - 1 := by
          (expose_names; exact Polynomial.natDegree_eq_of_degree_eq_some h)
        simp_all
        have _ : p > 0 := by
          exact Nat.Prime.pos hp
        grind
    have hz : ∃ z : F, f.IsRoot z := by
      refine Polynomial.exists_root_of_degree_eq_one ?_
      have _ : f.degree = f.natDegree := by
        refine Polynomial.degree_eq_natDegree ?_
        exact minpoly.ne_zero_of_finite F y
      simp_all
    obtain ⟨z, hz⟩ := hz
    have hprim : IsPrimitiveRoot z p := by
      have hnz : NeZero (p: F) := by
        have hnon : Nontrivial F := by
          exact Field.toSemifield.toCommGroupWithZero.toNontrivial
        have h1 : CharP F p ↔ (p : F) = 0 :=
          CharP.charP_iff_prime_eq_zero hp
        have h2 : ¬CharP F p := by
          by_contra
          have _ : ringChar F = p := by
            exact ringChar.eq F p
          simp_all
        obtain ⟨h1a, h1b⟩ := h1
        have _ : (p : F) ≠ 0 := by
          exact Ne.symm (Ne.symm fun a => h2 (h1b a))
        (expose_names; exact { out := h_6 })
      have h3 : (Polynomial.cyclotomic p F).IsRoot z ↔ IsPrimitiveRoot z p :=
        Polynomial.isRoot_cyclotomic_iff
      obtain ⟨h3a, h3b ⟩ := h3
      have h_cycloroot : cyclo.IsRoot z := by
        (expose_names; exact Polynomial.IsRoot.dvd hz h_3)
      specialize h3a h_cycloroot
      exact h3a
    refine Finset.nonempty_def.mpr ?_
    use z
    refine (mem_primitiveRoots ?_).mpr ?_
    exact Module.finrank_pos
    subst p
    apply hprim
  let G := Gal(K/F)
  have h_ord : Nat.card G = p := by
    have _ : Nat.card G = Module.finrank F K := by
      exact IsGalois.card_aut_eq_finrank F K
    simp_all
  have h_cyc : IsCyclic G := by
    have _ : Fact p.Prime := by
      exact fact_iff.mpr hp
    exact isCyclic_of_prime_card h_ord
  by_contra
  have hpp : p^2 > p := by
    have _ : p > 1 := by
      exact Nat.Prime.one_lt hp
    have _ : p * p > p := by
      (expose_names; exact Nat.lt_mul_self_iff.mpr h)
    grind
  have h_kummer : [IsGalois F K ∧ IsCyclic Gal(K/F),
       ∃ (a : F), Irreducible (Polynomial.X ^ Module.finrank F K - Polynomial.C a)
          ∧ Polynomial.IsSplittingField F K (Polynomial.X ^ Module.finrank F K - Polynomial.C a),
      ∃ (α : K), α ^ Module.finrank F K ∈ Set.range ⇑(algebraMap F K) ∧ F⟮α⟯ = ⊤].TFAE :=
        isCyclic_tfae F K hK
  have h_tfae : IsGalois F K ∧ IsCyclic Gal(K/F) ↔
    ∃ (a : F), Irreducible (Polynomial.X ^ Module.finrank F K - Polynomial.C a)
          ∧ Polynomial.IsSplittingField F K (Polynomial.X ^ Module.finrank F K - Polynomial.C a) := by
    apply List.TFAE.out h_kummer 0 1
  obtain ⟨h1, h2⟩ := h_tfae
  have h3 : IsGalois F K ∧ IsCyclic Gal(K/F) := by
    constructor
    exact hgal
    exact h_cyc
  specialize h1 h3
  obtain ⟨a, h4, h5⟩ := h1
  have h_irr: ∀ (n : ℕ), n ≠ 0 → (Irreducible (Polynomial.X ^ p ^ n - Polynomial.C a) ↔ ∀ (b : F), b ^ p ≠ a) := by
    intro n hn
    apply X_pow_sub_C_irreducible_iff_of_prime_pow hp
    push Not at this
    exact this
    exact hn
  have h6 : ∀ (b : F), b ^ p ≠ a := by
    have h7 : 1 ≠ 0 := by
      exact Nat.one_ne_zero
    specialize h_irr 1 h7
    obtain ⟨h8, _⟩ := h_irr
    have h9 : Irreducible (Polynomial.X ^ p ^ 1 - Polynomial.C a) := by
      simp_all
    specialize h8 h9
    exact h8
  have h10 : Irreducible (Polynomial.X ^ p ^ 2 - Polynomial.C a) := by
    have h11 : 2 ≠ 0 := by
      exact Ne.symm (Nat.zero_ne_add_one 1)
    specialize h_irr 2 h11
    obtain ⟨_, h12⟩ := h_irr
    specialize h12 h6
    exact h12
  let pol := Polynomial.X ^ p ^ 2 - Polynomial.C a
  have h13 : pol.natDegree = p^2 := by
    exact Polynomial.natDegree_X_pow_sub_C
  have h14 : pol.natDegree = pol.degree := by
    refine Eq.symm (Polynomial.degree_eq_natDegree ?_)
    exact Irreducible.ne_zero h10
  have hc : ∃ c : K, Polynomial.aeval c pol = 0 := by
    have _ : IsAlgClosed K := by
      exact IsAlgClosure.isAlgClosed F
    refine IsAlgClosed.exists_aeval_eq_zero_of_injective K ?_ pol ?_
    exact FaithfulSMul.algebraMap_injective F K
    simp_all
    have _ : pol.degree > 0 := by
      refine Polynomial.natDegree_pos_iff_degree_pos.mp ?_
      simp_all
      refine Nat.pow_pos ?_
      exact Nat.Prime.pos hp
    (expose_names; exact ne_of_gt h_1)
  obtain ⟨c, hc⟩ := hc
  let f := minpoly F c
  have h_int : IsIntegral F c := by
    exact Algebra.IsIntegral.isIntegral c
  have h_fmon: f.Monic := by
    refine minpoly.monic ?_
    exact h_int
  have h_div : f ∣ pol := by
    exact minpoly.dvd_iff.mpr hc
  have h_f : f.natDegree > 0 := by
    exact minpoly.natDegree_pos h_int
  have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree := by
    refine divisor_of_irreducible_poly f pol h_div ?_
    subst pol
    apply h10
  cases h_deg
  · simp_all
  · have _ : f.natDegree ≤ Module.finrank F K := by
      exact minpoly.natDegree_le c
    simp_all
    rename_i hp2
    have _ : p < p := by
      calc
        p < p^2 := hpp
        _ ≤ p := hp2
    (expose_names; exact (lt_self_iff_false p).mp h_1)

lemma finite_separable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Algebra.IsSeparable F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  have _ : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_4, to_normal := IsAlgClosure.normal F K })
  let G := Gal(K/F)
  have hG : Nat.card G = 1 := by
    by_contra
    let d := Nat.card G
    have hp : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d := by
      exact Nat.exists_prime_and_dvd this
    obtain ⟨p, hp1, hp2⟩ := hp
    have hp2 : Fact (Nat.Prime p) := by
      exact fact_iff.mpr hp1
    have hp3 : Fact (p.Prime) := by
      exact fact_iff.mpr hp1
    have hg : ∃ g : G, orderOf g = p := by
      apply exists_prime_orderOf_dvd_card
      have _ : Nat.card G = Fintype.card G := by
        exact Nat.card_eq_fintype_card
      subst d
      simp_all
    obtain ⟨g, hg⟩ := hg
    let H := Subgroup.zpowers g
    have _ : Nat.card H = p := by
      have _ : Nat.card (Subgroup.zpowers g) = orderOf g :=
        Nat.card_zpowers g
      subst H
      simp_all
    let E := IntermediateField.fixedField H
    have h_ekrank : Module.finrank E K = p := by
      have _ : Module.finrank (IntermediateField.fixedField H) K = Nat.card H := by
        apply IntermediateField.finrank_fixedField_eq_card
      subst E
      simp_all
    have _ : IsAlgClosure E K := by
      refine { isAlgClosed := ?_, isAlgebraic := ?_ }
      exact IsAlgClosure.isAlgClosed F
      exact IntermediateField.isAlgebraic_tower_top
    have hgal: IsGalois E K := by
      exact IsGalois.tower_top_intermediateField E
    have _ : p = 2 := by
      apply finite_algebraic_closure_cyclic_quadratic E K
      exact hp1
      exact Eq.symm ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (id (Eq.symm h_ekrank))))
      apply hgal
    have h_char2 : ringChar E ≠ 2 := by
      apply finite_algebraic_closure_cyclic_prime E K
      · simp_all
      · simp_all
      · exact hgal
    have h_sq : ∀ (a : E), IsSquare a := by
      have h_sq1 : ∀ (a : E), IsSquare a ∨ IsSquare (-a) := by
        apply quadratic_algebraic_closure_no_i E K
        simp_all
      intro a
      specialize h_sq1 a
      cases h_sq1
      · (expose_names; exact even_ofMul_iff.mp h_5)
      · rename_i ha
        unfold IsSquare at ha
        obtain ⟨r, ha⟩ := ha
        unfold IsSquare
        obtain ⟨i, hi⟩ := h
        use r * (algebraMap F E) i
        ring_nf
        have hj : (algebraMap F E) i ^ 2 = -1 := by
          have _ : (algebraMap F E) (i ^ 2) = (algebraMap F E) (-1) := by
            exact (algebraMap.coe_inj F ↥E).mpr hi
          grind
        grind
    have _ : FiniteDimensional E K := by
      exact finiteDimensional_right E
    have h_sq3 : ∃ (a: E), ¬ IsSquare a := by
      apply nonsquare_in_quadratic_extension E K
      simp_all
      exact h_char2
    simp_all
  exact trivial_absolute_galois_group F K hG

lemma finite_inseparable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsPurelyInseparable F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  let p := ringChar F
  by_cases p = 0
  · have _: CharZero F := by
      (expose_names; exact (CharP.ringChar_zero_iff_CharZero F).mp h_1)
    have _: ringExpChar F = 1 := by
      exact ringExpChar.eq_one F
    have _: PerfectField F := by
      exact PerfectField.ofCharZero
    have _: Algebra.IsSeparable F K := by
      apply Algebra.IsAlgebraic.isSeparable_of_perfectField
    apply finite_separable_algebraic_closure_with_i F K h
  · by_cases p > 2
    · sorry
    · have _ : p = 2 := by
        sorry
      have _ : Module.finrank F K ≤ 1 := by
        by_contra
        push Not at this
        have h_E : ∃ (E : IntermediateField F K), Module.finrank E K = ringChar F := by
          apply finite_inseparable_extension_intermediate
          apply this
        obtain ⟨E, h_E⟩ := h_E
        sorry
      sorry

lemma finite_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  obtain ⟨i, hi⟩ := h
  let E := separableClosure F K
  have _ : IsPurelyInseparable E K := by
    exact separableClosure.isPurelyInseparable F K
  have _ : IsAlgClosure E K := by
    refine { isAlgClosed := ?_, isAlgebraic := ?_ }
    exact IsAlgClosure.isAlgClosed F
    exact IntermediateField.isAlgebraic_tower_top
  have _ : IsAlgClosed E := by
    apply finite_inseparable_algebraic_closure_with_i E K
    use (algebraMap F E) i
    have _ : (algebraMap F E) (i^2) = (algebraMap F E) (-1) := by
      grind
    have _ : (algebraMap F E) (-1) = -1 := by
      grind
    grind
  have _ : IsAlgClosure F E := by
    refine { isAlgClosed := ?_, isAlgebraic := ?_ }
    exact IsSepClosed.isAlgClosed_of_perfectField ↥E
    exact separableClosure.isAlgebraic F K
  apply finite_separable_algebraic_closure_with_i F E
  use i
