module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
public import Mathlib.FieldTheory.Relrank
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.FieldTheory2
public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField

lemma finite_algebraic_closure_cyclic_quadratic (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (hrank: Module.finrank F K = p)
  (hgal: IsGalois F K): p = 2 := by
  have h_char : ¬ ringChar F = p :=
    finite_algebraic_closure_cyclic_prime F K p hp hrank hgal
  have hK : (primitiveRoots (Module.finrank F K) F).Nonempty := by
    let cyclo := Polynomial.cyclotomic p F
    have _ : cyclo.degree = p.totient := Polynomial.degree_cyclotomic p F
    have _ : p.totient = p - 1 := Nat.totient_prime hp
    have h_cycloroot : ∃ y : K, Polynomial.aeval y cyclo = 0 := by
      have _ : IsAlgClosed K := IsAlgClosure.isAlgClosed F
      refine IsAlgClosed.exists_aeval_eq_zero K cyclo ?_
      simp_all
      refine Nat.sub_ne_zero_of_lt ?_
      exact Nat.Prime.one_lt hp
    obtain ⟨y, h_cycloroot⟩ := h_cycloroot
    let f := minpoly F y
    have _ : f.natDegree ∣ Module.finrank F K := by
      refine minpoly.degree_dvd ?_
      exact Algebra.IsIntegral.isIntegral y
    have h_divcyclo : f ∣ cyclo := minpoly.dvd_iff.mpr h_cycloroot
    have _ : f.natDegree ≤ cyclo.natDegree := by
      (expose_names; refine Polynomial.natDegree_le_of_dvd h_divcyclo ?_)
      exact Polynomial.cyclotomic_ne_zero p F
    have _ : f.natDegree = 1 := by
      have _ : f.natDegree ∣ p := by simp_all
      have hfd : f.natDegree = 1 ∨ f.natDegree = p := by
        (expose_names; exact Nat.Prime.eq_one_or_self_of_dvd hp f.natDegree h_4)
      cases hfd
      · simp_all
      · exfalso
        simp_all
        have _ : cyclo.natDegree = p - 1 := by
          (expose_names; exact Polynomial.natDegree_eq_of_degree_eq_some h)
        simp_all
        have _ : p > 0 := Nat.Prime.pos hp
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
        have hnon : Nontrivial F := Field.toSemifield.toCommGroupWithZero.toNontrivial
        have h1 : (p : F) = 0 → CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr
        have h2 : ¬CharP F p := by
          by_contra
          have _ : ringChar F = p := ringChar.eq F p
          simp_all
        have _ : (p : F) ≠ 0 := Ne.symm (Ne.symm fun a => h2 (h1 a))
        (expose_names; exact { out := h_5 })
      have h_cycloroot : cyclo.IsRoot z := Polynomial.IsRoot.dvd hz h_divcyclo
      exact Polynomial.isRoot_cyclotomic_iff.mp h_cycloroot
    refine Finset.nonempty_def.mpr ?_
    use z
    refine (mem_primitiveRoots ?_).mpr ?_
    exact Module.finrank_pos
    subst p
    exact hprim
  let G := Gal(K/F)
  have h_ord : Nat.card G = p := by
    calc
      Nat.card G = Module.finrank F K := IsGalois.card_aut_eq_finrank F K
      _ = p := hrank
  have h_cyc : IsCyclic G := by
    have _ : Fact p.Prime := fact_iff.mpr hp
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
    have h7 : 1 ≠ 0 := Nat.one_ne_zero
    specialize h_irr 1 h7
    obtain ⟨h8, _⟩ := h_irr
    have h9 : Irreducible (Polynomial.X ^ p ^ 1 - Polynomial.C a) := by
      simp_all
    specialize h8 h9
    exact h8
  have h10 : Irreducible (Polynomial.X ^ p ^ 2 - Polynomial.C a) := by
    have h11 : 2 ≠ 0 := Ne.symm (Nat.zero_ne_add_one 1)
    specialize h_irr 2 h11
    obtain ⟨_, h12⟩ := h_irr
    specialize h12 h6
    exact h12
  let pol := Polynomial.X ^ p ^ 2 - Polynomial.C a
  have h13 : pol.natDegree = p^2 := Polynomial.natDegree_X_pow_sub_C
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
  have h_int : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  have h_fmon: f.Monic := minpoly.monic h_int
  have h_div : f ∣ pol := minpoly.dvd_iff.mpr hc
  have h_f : f.natDegree > 0 := minpoly.natDegree_pos h_int
  have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree := by
    refine divisor_of_irreducible_poly f pol h_div ?_
    subst pol
    apply h10
  cases h_deg
  · simp_all
  · have _ : f.natDegree ≤ Module.finrank F K := minpoly.natDegree_le c
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
    have hp : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d := Nat.exists_prime_and_dvd this
    obtain ⟨p, hp1, hp2⟩ := hp
    have hp2 : Fact (Nat.Prime p) := fact_iff.mpr hp1
    have hp3 : Fact (p.Prime) := fact_iff.mpr hp1
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
    have hgal: IsGalois E K := IsGalois.tower_top_intermediateField E
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
    have _ : FiniteDimensional E K := finiteDimensional_right E
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
    · rename_i hpgt2a
      by_cases PerfectField F
      · have _ : Algebra.IsSeparable F K := by
          exact Algebra.IsAlgebraic.isSeparable_of_perfectField
        have _ : IsPurelyInseparable F K := by
          exact IsPurelyInseparable.instOfHasExponent F K
        have _ : Field.finSepDegree F K = 1 := by
          (expose_names; exact (isPurelyInseparable_iff_finSepDegree_eq_one F K).mp h_4)
        have _ : Field.finInsepDegree F K = 1 := by
          (expose_names; exact (isSeparable_iff_finInsepDegree_eq_one F K).mp h_3)
        have _ : Field.finSepDegree F K * Field.finInsepDegree F K = Module.finrank F K := by
          apply Field.finSepDegree_mul_finInsepDegree F K
        have _ : IsGalois F K := by
          (expose_names;
            exact { to_isSeparable := h_3, to_normal := IsPurelyInseparable.normal F K })
        have h_Gcard : Nat.card Gal(K/F) = 1 := by
          have _ : Nat.card Gal(K/F) = Module.finrank F K := by
            exact IsGalois.card_aut_eq_finrank F K
          simp_all
        apply trivial_absolute_galois_group F K h_Gcard
      · rename_i hpgt2
        have hp1 : Nat.Prime p := by
          have hp1 : Nat.Prime p ∨ p = 0 := by
            apply CharP.char_is_prime_or_zero F p
          simp_all
        have _ : ExpChar F p := by
            exact ExpChar.prime hp1
        have _ : ¬ PerfectRing F p := by
          by_contra
          have _ : ringChar F = ringChar K := by
            exact Algebra.ringChar_eq F K
          have _ :  PerfectField F := by
            apply PerfectRing.toPerfectField F p
          (expose_names; exact (iff_false_intro hpgt2).mp h_4)
        have h_inj : Function.Injective (frobenius F p) := by
          exact frobenius_inj F p
        have h_surj : ¬ Function.Surjective (frobenius F p) := by
          by_contra
          have _ : Function.Bijective (frobenius F p) := by
            unfold Function.Bijective
            constructor
            · exact h_inj
            · exact this
          have _ : PerfectRing F p := by
            (expose_names; exact { bijective_frobenius := h_4 })
          (expose_names; exact (iff_false_intro h_3).mp h_5)
        have h_a : ∃ a : F, ¬∃ x : F, x^p = a := by
          exact not_forall.mp h_surj
        obtain ⟨a, h_a⟩ := h_a
        have h_n : ∃ n : ℕ, p ^ (n) > Module.finrank F K := by
          refine pow_unbounded_of_one_lt (Module.finrank F K) ?_
          exact Nat.Prime.one_lt hp1
        obtain ⟨n, h_n⟩ := h_n
        let pol := Polynomial.X ^ p ^ (n + 1) - Polynomial.C a
        have _ : Irreducible pol ↔ ∀ (b : F), b ^ p ≠ a := by
          refine X_pow_sub_C_irreducible_iff_of_prime_pow hp1 ?_ ?_
          have _ : p ≥ 2 := by
            exact Nat.Prime.two_le hp1
          simp_all
          exact Nat.ne_of_lt' hpgt2a
          exact Ne.symm (Nat.zero_ne_add_one n)
        have h_pol_irr : Irreducible pol := by
          refine (X_pow_sub_C_irreducible_iff_of_prime_pow hp1 ?_ ?_).mpr ?_
          exact Nat.ne_of_lt' hpgt2a
          exact Ne.symm (Nat.zero_ne_add_one n)
          intro b
          push Not at h_a
          specialize h_a b
          exact h_a
        have _ : pol.natDegree = p ^ (n+1) := by
          exact Polynomial.natDegree_X_pow_sub_C
        have hn : 0 < p ^ (n+1) := by
          exact expChar_pow_pos F p (n + 1)
        have _ : pol.degree = p ^ (n+1) := by
          have _ : pol.degree = p ^ (n+1) ↔ pol.natDegree = p ^ (n+1) := by
            apply Polynomial.degree_eq_iff_natDegree_eq_of_pos hn
          simp_all
        have _ : pol.Monic := by
          have hn1 : p ^ (n+1) ≠ 0 := by
            (expose_names; exact pow_ne_zero (n + 1) h_1)
          have _ : (Polynomial.X ^ p ^ (n + 1) + Polynomial.C (-a)).Monic := by
            refine Polynomial.monic_X_pow_add_C (-a) hn1
          grind
        have _ : pol.natDegree ≤ Module.finrank F K := by
          have hy : ∃ y : K, Polynomial.aeval y pol = 0 := by
            have _ : IsAlgClosed K := by
              exact IsAlgClosure.isAlgClosed F
            apply IsAlgClosed.exists_aeval_eq_zero K pol
            simp_all
          obtain ⟨y, hy⟩ := hy
          let f := minpoly F y
          have h_int : IsIntegral F y := by
            exact Algebra.IsIntegral.isIntegral y
          have h_fmon: f.Monic := by
            refine minpoly.monic ?_
            exact h_int
          have h_div : f ∣ pol := by
            exact minpoly.dvd_iff.mpr hy
          have h_f : f.natDegree > 0 := by
            exact minpoly.natDegree_pos h_int
          have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree := by
            refine divisor_of_irreducible_poly f pol h_div ?_
            subst pol
            apply h_pol_irr
          cases h_deg
          · simp_all
          have _ : f.natDegree ≤ Module.finrank F K := by
            exact minpoly.natDegree_le y
          simp_all
        have _ : p ^ (n + 1) > p^n := by
          refine Nat.pow_lt_pow_of_lt ?_ ?_
          exact Nat.Prime.one_lt hp1
          exact lt_add_one n
        exfalso
        grind
    · have hp2 : p = 2 := by
        rename_i h1
        push Not at h1
        refine Eq.symm (Nat.le_antisymm ?_ h1)
        refine Nat.Prime.two_le ?_
        have hp1 : Nat.Prime p ∨ p = 0 := by
          apply CharP.char_is_prime_or_zero F p
        cases hp1
        · rename_i h1
          apply h1
        · exfalso
          simp_all
      have _ : Module.finrank F K ≤ 1 := by
        by_contra
        push Not at this
        have h_E : ∃ (E : IntermediateField F K), Module.finrank E K = ringChar F := by
          apply finite_inseparable_extension_intermediate
          apply this
        obtain ⟨E, h_E⟩ := h_E
        have h_E1 : Module.finrank E K = 2 := by
          calc
            Module.finrank E K = ringChar F := h_E
            _ = p := by rfl
            _ = 2 := hp2
        have _ : IsAlgClosure E K := by
          refine { isAlgClosed := ?_, isAlgebraic := ?_ }
          exact IsAlgClosure.isAlgClosed F
          exact isAlgebraic_tower_top
        have h_sq1 : ∀ (a b : ↥E), IsSquare (a ^ 2 + b) ∨ IsSquare (-b) := by
          apply quadratic_algebraic_closure E K h_E1
        have h_charE : ringChar E = ringChar F := by
          exact Eq.symm (Algebra.ringChar_eq F ↥E)
        have h_sq : ∀ (a : E), IsSquare a := by
          intro a
          specialize h_sq1 0 a
          cases h_sq1
          · have _ : 0^2 = 0 := by
              exact Eq.symm (Nat.eq_of_beq_eq_true rfl)
            simp_all
          · have _ : (-1 : E) = (1 : E) := by
              refine neg_one_eq_one_iff.mpr ?_
              simp_all
            have _ : (-1 : E) * a = (1 : E) * a := by
              (expose_names;
                exact
                  SetLike.coe_eq_coe.mp
                    (congrArg Subtype.val (congrFun (congrArg HMul.hMul h_5) a)))
            have _ : -a = a := by
              grind
            simp_all
        have _ : CharP E 2 := by
          refine ringChar.of_eq ?_
          calc
            ringChar E = ringChar F := h_charE
            _ = p := by rfl
            _ = 2 := hp2
        have _ : ExpChar E 2 := by
          apply expChar_prime
        have h_frobsurj : Function.Surjective (frobenius E 2) := by
          unfold Function.Surjective
          intro b
          specialize h_sq b
          unfold IsSquare at h_sq
          obtain ⟨r, h_sq⟩ := h_sq
          use r
          unfold frobenius
          simp
          grind
        have _ : PerfectRing E 2 := by
          apply PerfectRing.ofSurjective
          exact h_frobsurj
        have _ : PerfectField E := by
          have _ : ExpChar (↥E) p := by
            exact ExpChar.congr (↥E) 2 (id (Eq.symm hp2))
          apply PerfectRing.toPerfectField E 2
        have _ : Algebra.IsSeparable E K := by
          exact Algebra.IsAlgebraic.isSeparable_of_perfectField
        have _ : IsPurelyInseparable E K := by
          exact isPurelyInseparable_tower_top F K E
        have _ : Field.finSepDegree E K = 1 := by
          (expose_names; exact (isPurelyInseparable_iff_finSepDegree_eq_one (↥E) K).mp h_9)
        have _ : Field.finInsepDegree E K = 1 := by
          (expose_names; exact (isSeparable_iff_finInsepDegree_eq_one (↥E) K).mp h_8)
        have _ : Field.finSepDegree E K * Field.finInsepDegree E K = Module.finrank E K := by
          apply Field.finSepDegree_mul_finInsepDegree E K
        grind
      have _ : Module.finrank F K = 1 := by
        (expose_names; refine Eq.symm (Nat.le_antisymm ?_ h_3))
        refine Nat.one_le_iff_ne_zero.mpr ?_
        refine Nat.ne_zero_iff_zero_lt.mpr ?_
        apply Module.finrank_pos
      have _ : Field.finSepDegree F K * Field.finInsepDegree F K = Module.finrank F K := by
        apply Field.finSepDegree_mul_finInsepDegree F K
      have h_insep1 : Field.finInsepDegree F K = 1 := by
        have _ : Field.finInsepDegree F K ≥ 1 := by
          exact NeZero.one_le
        have _ : Field.finInsepDegree F K ∣ Module.finrank F K := by
          (expose_names; exact dvd_of_mul_left_eq (Field.finSepDegree F K) h_5)
        simp_all
      have _ :  Algebra.IsSeparable F K := by
        have hsep : Algebra.IsSeparable F K ↔ Field.finInsepDegree F K = 1 := by
          apply isSeparable_iff_finInsepDegree_eq_one F K
        obtain ⟨hsep1, hsep2⟩ := hsep
        specialize hsep2 h_insep1
        apply hsep2
      have _ : IsGalois F K := by
        (expose_names; exact { to_isSeparable := h_6, to_normal := IsPurelyInseparable.normal F K })
      have h_Gcard : Nat.card Gal(K/F) = 1 := by
        have _ : Nat.card Gal(K/F) = Module.finrank F K := by
          exact IsGalois.card_aut_eq_finrank F K
        simp_all
      apply trivial_absolute_galois_group F K h_Gcard

lemma finite_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  obtain ⟨i, hi⟩ := h
  let E := separableClosure F K
  have _ : IsPurelyInseparable E K := separableClosure.isPurelyInseparable F K
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
