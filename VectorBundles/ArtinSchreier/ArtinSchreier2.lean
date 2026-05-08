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
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.Cycle.Type

public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

lemma quadratic_algebraic_closure_no_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hi: ∃ (i : F), i^2 = -1) (h : Module.finrank F K = 2) :
  ∀ (a : F), IsSquare a := by
  have _: IsAlgClosed K := by
    exact IsAlgClosure.isAlgClosed F
  obtain ⟨i, hi⟩ := hi
  intro a
  let iota := algebraMap F K
  have hb : ∃ b : K, b^4 = iota a := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp
  obtain ⟨b, hb⟩ := hb
  have hint : IsIntegral F b := by
    exact Algebra.IsIntegral.isIntegral b
  let f := minpoly F b
  let d := Polynomial.natDegree f
  have _ : 0 < d := by
    exact minpoly.natDegree_pos hint
  have hf : d ≤ 2 := by
    grind [minpoly.natDegree_le]
  have hd : d = 1 ∨ d = 2 := by
    grind
  have haeval : Polynomial.aeval b f = 0 := by
    exact minpoly.aeval F b
  have hc : ∃ c : F, iota c = b^2 := by
    cases hd
    · have _ : (minpoly F b).natDegree = 1 := by
        grind
      have _ : (minpoly F b).natDegree = 1 ↔ b ∈ iota.range := by
        exact minpoly.natDegree_eq_one_iff
      have _ : b ∈ iota.range := by
        (expose_names; exact minpoly.natDegree_eq_one_iff.mp h_3)
      have hb₀ : ∃ b₀ : F, iota b₀ = b := by
        (expose_names; exact Set.mem_range.mp h_6)
      obtain ⟨b₀, hb₀⟩ := hb₀
      use b₀^2
      grind

    · -- let f0 := Polynomial.constantCoeff f
      let g := Polynomial.X^4 - Polynomial.C a
      have _ : Polynomial.aeval b g = 0 := by
        unfold Polynomial.aeval
        simp_all
        subst g
        unfold Polynomial.aevalEquiv
        simp
        grind
      have hdiv : f ∣ g := by
        (expose_names; exact minpoly.dvd_iff.mpr h_4)
      let f_K := Polynomial.map (algebraMap F K) f
      let g_K := Polynomial.map (algebraMap F K) f
      have hdiv_K : f_K ∣ g_K := by
        exact Eq.dvd rfl
      have _ : f_K.roots ≤ g_K.roots := by
        apply Polynomial.roots.le_of_dvd
        refine (Polynomial.map_ne_zero_iff ?_).mpr ?_
        exact FaithfulSMul.algebraMap_injective F K
        exact minpoly.ne_zero_iff.mpr hint
        exact hdiv_K
      have _ : g_K.Splits := by
        exact Normal.splits' b
      have _ : ∀ (x : K), x ∈ f_K.roots → x/b ∈ (algebraMap F K).range := by
        intro x hx
        have hx1: x ∈ g_K.roots := by
          (expose_names; exact Multiset.mem_of_le h_5 hx)
        have hx2 : Polynomial.eval x g_K = 0 := by
          unfold Polynomial.roots at hx1
          refine Polynomial.IsRoot.def.mp ?_
          exact Polynomial.isRoot_of_mem_roots hx
        have _ : x^4 = b^4 := by
          subst g
          expose_names
          unfold Polynomial.aeval at h_6
          unfold Polynomial.aevalEquiv at h_6
          sorry
        let y := x/b
        let g1 := Polynomial.X ^ 4 - Polynomial.C (1 : K)
        have _ : y ∈ g1.roots := by
          sorry
        have hy : y = 1 ∨ y = -1 ∨ y = (algebraMap F K) i ∨ y = - (algebraMap F K) i := by
          sorry
        have _ : y ∈ (algebraMap F K).range := by
          refine RingHom.mem_range.mpr ?_
          cases hy
          · use 1
            grind
          rename_i hy
          cases hy
          · use -1
            grind
          rename_i hy
          cases hy
          · use i
            grind
          · use -i
            grind
        grind
      have hspl : f_K.Splits := by
        exact Normal.splits' b
      have _ : ∃ (r1 r2 : K), f_K = (Polynomial.X - Polynomial.C r1) *
        (Polynomial.X - Polynomial.C r2) := by
        have _ : ∀ x : K, Polynomial.eval x f_K = (Multiset.map (fun (x_1 : K) => x - x_1) f_K.roots).prod := by
          -- refine Polynomial.Splits.eval_eq_prod_roots_of_monic
          sorry
        sorry
      let S := {x : K | x = b ∨ x = (algebraMap F K) i*b ∨ x = -b ∨ x = -(algebraMap F K) i*b}
      have _ : ∀ (x : K), Polynomial.aeval x f = 0 → x ∈ S := by
        intro x hx
        have hx1 : Polynomial.aeval x g = 0 := by
          exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv hx
        have _ : x^4 = iota a := by
          unfold Polynomial.aeval at hx1
          simp_all
          subst g
          unfold Polynomial.aevalEquiv at hx1
          simp_all
          grind
        sorry
      sorry
  unfold IsSquare
  obtain ⟨c, hc⟩ := hc
  use c
  have hinj : Function.Injective iota := by
    exact FaithfulSMul.algebraMap_injective F K
  apply hinj
  grind

lemma finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (h: Module.finrank F K = p)
  (hsep: IsGalois F K): ¬ ringChar F = p := by
  sorry

lemma finite_algebraic_closure_cyclic_quadratic (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (hrank: Module.finrank F K = p)
  (hgal: IsGalois F K): p = 2 := by
  sorry

lemma finite_separable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Algebra.IsSeparable F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  sorry

lemma finite_inseparable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsPurelyInseparable F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  sorry

lemma finite_algebraic_closure_separable (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] : IsGalois F K :=
  have _: PerfectField F := by
    by_cases CharZero F
    · apply PerfectField.ofCharZero
    · let p := ringChar F
      have _: Nat.Prime p ∨ p = 0 := by
        apply CharP.char_is_prime_or_zero F p
      have _: Nat.Prime p := by
        grind [CharP.ringChar_zero_iff_CharZero F]
      have hchar: ExpChar F p := by
        (expose_names; exact ExpChar.prime h_2)
      let frob := frobenius F p
      have hpow: ∀ a : F, ∃ b : F, b^p = a := by
        intro a
        by_cases hp: p = 2
        · have hi : ∃ (i : F), i^2 = -1 := by
            use 1
            sorry
          sorry
          --   sorry
            -- apply quadratic_algebraic_closure_no_i F K a
        · let d := Module.finrank F K
          have _ : 1 < p := by
            (expose_names; exact Nat.Prime.one_lt h_2)
          have h1: ∃ n : ℕ, d < p^n := by
            refine pow_unbounded_of_one_lt d ?_
            grind
          obtain ⟨n, h2⟩ := h1
          have _: IsAlgClosed K := by
            exact IsAlgClosure.isAlgClosed F
          have h3: ∃ b : K, b^(p^n) = (algebraMap F K) a := by
            refine IsAlgClosed.exists_pow_nat_eq ((algebraMap F K) a) ?_
            grind
          obtain ⟨b, h4⟩ := h3
          let f := minpoly F b
          have _ : ¬ Irreducible f := by
            sorry
          let g := Polynomial.factor f
          let d₁ := Polynomial.natDegree g
          have _ : d₁ < p^n := by
            sorry
          let e := gcd d₁ p^n
          let (g_1, g_2) := Nat.xgcd d₁ p^n
          sorry
      have _: Function.Surjective frob := by
          unfold Function.Surjective
          unfold frob
          intro a
          apply hpow
      have _: PerfectRing F p := by
        exact PerfectRing.ofSurjective F p hpow
      exact PerfectRing.toPerfectField F p
  { to_isSeparable := IsSepClosure.isSeparable, to_normal := IsGalois.to_normal }

lemma finite_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : ∃ (i : K), i^2 = -1 ∧ i ∈ (algebraMap F K).range) : IsAlgClosed F := by

  by_contra
  have hgal: IsGalois F K :=
    finite_algebraic_closure_separable F K
  let G := K ≃ₐ[F] K
  let d := Nat.card G
  have hd : 1 < d := by
    -- apply IsGaloisGroup.card_eq_finrank
    sorry
  let p := Nat.minFac d
  have hp : Nat.Prime p := by
    sorry
    --apply Nat.minFac_prime d hd
  have cyc: ∃ (g : G), orderOf g = p := by
    -- apply exists_prime_orderOf_dvd_card p
    sorry
  obtain ⟨g, hg1⟩ := cyc
  let H := Subgroup.zpowers g
  let F₁ := IntermediateField.fixedField H
  have hrank : Module.finrank F₁ K = p := by
    sorry
    --apply IsGalois.card_fixingSubgroup_eq_finrank
  have _: IsAlgClosure F₁ K := by
    sorry
  have hgal1: IsGalois F₁ K :=
    finite_algebraic_closure_separable F₁ K
  have hp2: p = 2 :=
    finite_algebraic_closure_cyclic_quadratic F₁ K p hp hrank hgal1
  have ha: ∃ a : F₁, ¬ IsSquare a := by
    sorry
  obtain ⟨a, ha⟩ := ha
  have hfin: Module.finrank F₁ K = 2 := by
    sorry
  sorry
  -- apply quadratic_algebraic_closure_no_i F₁ K

lemma RealClosed_from_quadratic (F : Type) (K : Type) (L: Type)
  [Field F] [Field K] [Field L] [Algebra F K] [Algebra K L] [Algebra F L] [FiniteDimensional F K] [IsAlgClosed K]
  (h1 : ¬ ∃ i : K, i^2 = -1 ∧ i ∈ (algebraMap F K).range)
  (h2 : ∃ i : L, i^2 = -1 ∧ IntermediateField.adjoin F {x : L | x = i} = K)
  : IsRealClosed F := by

  have have_i: ∃ i : K, i^2 = -1 := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp -- to prove 0 < 2
  obtain ⟨i, hi⟩ := have_i

  have semi: IsSemireal F := by
    have hs: ∀ x : F, ∀ y : F, ∃ z : F, x^2 + y^2 = z^2 := by
      intro x y
      have have_u: ∃ u : K, u^2 = ⇑(algebraMap F K) x + i * ⇑(algebraMap F K) y := by
        sorry
      obtain ⟨u, hu⟩ := have_u
      have have_ab: ∃ a : F, ∃ b : F, u = ⇑(algebraMap F K) a + i * ⇑(algebraMap F K) b := by
        sorry
      obtain ⟨a, b, hab⟩ := have_ab
      use a^2 + b^2
      sorry
    have hssq: ∀ x : F, IsSumSq x → IsSquare x := by
      intro x hx
      induction hx with
      | zero => simp
      | sq_add y _ hz =>
          rcases hz with ⟨z, hz⟩
          unfold IsSquare
          subst hz
          obtain ⟨r, hr⟩ := hs y z
          use r
          grind
    rw [isSemireal_iff_not_isSumSq_neg_one]
    by_contra
    have h2 : IsSquare (-1 : F) := by
      grind
    obtain ⟨a,b⟩ := h2
    apply h1
    use (algebraMap F K) a
    constructor
    · symm
      have _ : (algebraMap F K) (-1 : F) = (algebraMap F K) (a * a) :=
        congr_arg (algebraMap F K) b
      grind
    · exact RingHom.mem_range_self (algebraMap F K) a
  have hR: CharZero F := by
    exact CharP.charP_to_charZero F
  refine
    { toIsSemireal := semi, isSquare_or_isSquare_neg := ?_, exists_isRoot_of_odd_natDegree := ?_ }
  -- ∀ (x : F), IsSquare x ∨ IsSquare (-x)
  sorry
  -- ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x
  intro f
  let p := f.roots
  let G := K ≃ₐ[F] K
  sorry

theorem artin_schreier_thm (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] : IsAlgClosed F ∨ IsRealClosed F := by
  have _: IsAlgClosed K := by
    exact IsAlgClosure.isAlgClosed F
  have have_i: ∃ i : K, i^2 = -1 := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp -- to prove 0 < 2
  obtain ⟨i, hi⟩ := have_i
  if hF : i ∈ (algebraMap F K).range then
    left
    apply finite_algebraic_closure_with_i F K
    use i
  else
    right
    let S : Set K := {x | x = i}
    let F₁ := IntermediateField.adjoin F S
    have _ : i ∈ F₁ := by
      have hiS: i ∈ S := by
        exact Set.mem_setOf.mpr rfl
      exact IntermediateField.mem_adjoin_of_mem F hiS
    let iota₁ := algebraMap F₁ K
    have _: IsAlgClosure F₁ K := by
      apply IsAlgClosure.ofAlgebraic F₁ K
    have _: IsAlgClosed F₁ := by
      apply finite_algebraic_closure_with_i F₁ K
      use i
      constructor
      · apply hi
      · have _ : F₁ = Set.range iota₁ := by
          apply IntermediateField.adjoin_eq_range_algebraMap_adjoin
        simp_all
    apply RealClosed_from_quadratic F F₁ K
    · let iota := algebraMap F F₁
      by_contra
      obtain ⟨i₁, h22, _⟩ := this
      let i₂ := iota₁ i₁
      have _ : iota₁ (i₁ ^ 2) = iota₁ (-1 : F₁) :=
        congr_arg iota₁ h22
      have _ : i₂ = i ∨ i₂ = -i := by
        grind
      have _ : algebraMap F K = iota₁.comp iota := by
        exact IsScalarTower.algebraMap_eq F (↥F₁) K
      have h33 : i₂ ∈ (iota₁.comp iota).range := by
        have h : Subring.map iota₁ iota.range = (iota₁.comp iota).range :=
          RingHom.map_range iota₁ iota
        have h1 : i₁ ∈ iota.range := by
          (expose_names; exact RingHom.mem_range.mpr right)
        subst i₂
        have _ : iota₁ i₁ ∈ Subring.map iota₁ iota.range := by
          grind [Subring.mem_map]
        grind
      have _ : -i₂ ∈ (algebraMap F K).range := by
        exact Subring.neg_mem (algebraMap F K).range h33
      grind
    · use i
