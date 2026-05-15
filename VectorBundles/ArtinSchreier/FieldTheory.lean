module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
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

public import VectorBundles.ArtinSchreier.Polynomials

@[expose] public section

open IntermediateField

lemma finite_extension_degree_one (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
  Module.finrank F K > 1 → ¬ Function.Surjective (algebraMap F K) := by
    intro h
    by_contra
    have _ : Module.rank F F = Module.rank F K + Module.rank F (Algebra.linearMap F K).ker := by
      apply LinearMap.rank_eq_of_surjective this
    have _ : Module.rank F F = 1 := by
      exact CommSemiring.rank_self F
    have _ :  Module.rank F (Algebra.linearMap F K).ker ≥ 0 := by
      exact Cardinal.zero_le (Module.rank F ↥(Algebra.linearMap F K).ker)
    have _ : Module.rank F K ≤ 1 := by
      simp_all
    have _: Module.finrank F K ≤ 1 := by
      (expose_names; exact Module.finrank_le_of_rank_le h_4)
    grind

lemma fixed_field_of_cyclic_subgroup (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsGalois F K] (g : Gal(K/F)) : ∀ x : K,
  g x = x → x ∈ IntermediateField.fixedField (Subgroup.zpowers g):= by
  intro x hg
  have h_pow : ∀ n : ℕ, (g^n) x = x := by
    intro n
    induction n with
    | zero =>
      have _ : g ^ 0 = 1:= by
        exact pow_zero g
      simp
    | succ n hyp =>
      have h_mul : ∀ (g1 g2 : Gal(K/F)), g1 (g2 x) = (g1 * g2) x := by
        exact fun g1 g2 => AlgEquiv.congr_fun rfl (g2 x)
      specialize h_mul (g^n) g
      simp_all
  have h_sub : ∀ h : Gal(K/F), h ∈ Subgroup.zpowers g → h x = x := by
    intro h h1
    have h2 : ∃ n : ℕ, g ^ n = h := by
      refine (Submonoid.mem_powers_iff h g).mp ?_
      exact mem_powers_iff_mem_zpowers.mpr h1
    obtain ⟨n, h2 ⟩ := h2
    specialize h_pow n
    subst h
    exact h_pow
  exact (mem_fixedField_iff (Subgroup.zpowers g) x).mpr h_sub

lemma cyclic_char_p_as_artin_schreier (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (hp: Nat.Prime p) (hrank: Module.finrank F K = p)
  (hsep: IsGalois F K) (hchar: ringChar F = p) : ∃ (a : F), ∃ (x : K),
  minpoly F x = Polynomial.X ^ p - Polynomial.X - Polynomial.C a := by
  have _ : Function.Surjective (Algebra.trace F K) := by
    apply Algebra.trace_surjective
  have hy : ∃ (y : K), Algebra.trace F K y = 1 := by
    (expose_names; exact Set.mem_range.mp (h 1))
  obtain ⟨y, hy⟩ := hy
  have _ : CharP F p := by
    exact ringChar.of_eq hchar
  have : CharP K p := by
    have _ : CharP F p ↔ CharP K p := by
      apply Algebra.charP_iff
    (expose_names; exact (Algebra.charP_iff F K p).mp h_1)
  have : ExpChar K p := by
    exact ExpChar.prime hp
  let G := Gal(K/F)
  have h_ord : Nat.card G = p := by
    calc
      Nat.card G = Module.finrank F K := by exact IsGalois.card_aut_eq_finrank F K
      _  = p := by apply hrank
  have : Fact (Nat.Prime p) := by
    exact fact_iff.mpr hp
  have : IsCyclic G := by
    apply isCyclic_of_prime_card h_ord
  have h_gen : ∃ g : G, Subgroup.zpowers g = ⊤ := by
    exact isCyclic_iff_exists_zpowers_eq_top.mp this
  obtain ⟨g, h_gen⟩ := h_gen
  have h_ordg : orderOf g = p := by
    calc
      orderOf g = Nat.card G := by
        apply orderOf_eq_card_of_zpowers_eq_top
        exact h_gen
      _ = p := h_ord
  let f (i : ℕ) : K := -(g^i) y * i
  let z := ∑ i : Finset.range p, -((g^(i:ℕ)) y) * (i:K)
  have hz : g z = z + 1 := by
    have : ∑ i : Finset.range p, (g^((i+1):ℕ)) y = 1 := by
      have h_trace_as_sum :  algebraMap F K (Algebra.trace F K y) = ∑ σ : Gal(K/F), σ y := by
        apply trace_eq_sum_automorphisms
      let f : Finset.range p → Gal(K/F) := fun i => g ^((i+1):ℕ)
      have _ : Function.Bijective f := by
        have h_bij : Function.Bijective f ↔ Function.Injective f ∧ Nat.card (Finset.range p) = Nat.card Gal(K/F) :=
          Nat.bijective_iff_injective_and_card f
        obtain ⟨h1, h2⟩ := h_bij
        apply h2
        constructor
        · by_contra
          unfold Function.Injective at this
          push Not at this
          obtain ⟨i1, hi1⟩ := this
          obtain ⟨i2, hi2, hi3⟩ := hi1
          have h_po : g^((i1+1):ℤ) = g^((i2+1):ℤ) := by
            exact AlgEquiv.ext_iff.mpr (congrFun (congrArg DFunLike.coe hi2))
          let j := (i1 : ℤ) - (i2 : ℤ)
          have : (p : ℤ) ∣ j := by
            have h : (orderOf g : ℤ) ∣ ((i1+1):ℤ) - ((i2+1):ℤ) ↔ g ^ ((i1+1):ℤ) = g ^ ((i2+1):ℤ) := by
              apply orderOf_dvd_sub_iff_zpow_eq_zpow
            obtain ⟨h1, h2⟩ := h
            specialize h2 h_po
            subst j
            simp_all
          have : j ≠ 0 ∧ j ≤ p-1 ∧ j ≥ 1-p := by
            grind
          have h_e : ∃ e : ℤ, e * p = j := by
            have _ : (p : ℤ) ∣ j ↔ ∃ e : ℤ, j = e * p :=
              dvd_iff_exists_eq_mul_left
            grind
          obtain ⟨e, h_e⟩ := h_e
          have h_e0 : e ≠ 0 := by
            grind
          have h_e2 : e ≥ 1 ∨ e ≤ -1 := by
            grind
          have : p > 0 := by
            grind
          cases h_e2
          · have : e * p ≥ 1 * p := by
              (expose_names; refine Int.mul_le_mul_of_nonneg_right h_2 ?_)
              exact Int.natCast_nonneg p
            grind
          · have : e * p ≤ -1 * p := by
              (expose_names; refine Int.mul_le_mul_of_nonneg_right h_2 ?_)
              exact Int.natCast_nonneg p
            grind
        · have _ : Nat.card ↥(Finset.range p) = p := by
            have _ : Nat.card (Finset.range p) = Finset.card (Finset.range p) :=
              Nat.card_eq_finsetCard (Finset.range p)
            have _ :  (Finset.range p).card = p :=
              Finset.card_range p
            simp_all
          grind
      have h_trace_as_sum2 :  ∑ i : Finset.range p, (fun i => (g^((i+1):ℕ)) y) i  = ∑ σ : Gal(K/F), (fun σ => σ y) σ := by
        apply Finset.sum_bijective f
        · rename_i h
          apply h
        · intro i
          constructor
          · intro hi
            exact Finset.mem_univ (f i)
          · intro hi
            exact Finset.mem_univ i
        · intro i hi
          subst f
          simp
      simp_all
    have _ : g z = ∑ i : Finset.range p, - ((g^((i+1):ℕ)) y) * (i:K) := by
      have _ : g z =  ∑ i : Finset.range p, -g (((g^(i:ℕ)) y) * (i:K)) := by
        have _ : g (∑ i : Finset.range p,
          ((g^(i:ℕ)) y) * (i:K)) = ∑ i : Finset.range p, g (((g^(i:ℕ)) y) * (i:K)) := by
          apply map_finset_sum
        subst z
        simp_all
      have _ : ∀ i : Finset.range p,
        g (((g^(i:ℕ)) y) * (i:K)) = ((g^((i+1):ℕ)) y) * (i:K)  := by
        intro i
        calc
          g (((g^(i:ℕ)) y) * (i:K)) = g ((g^(i:ℕ)) y) * (i:K) := by simp_all
          _ = ((g^((i+1):ℕ)) y) * (i:K) := ?_
        have _ : g * g^(i:ℕ) = g^((i+1):ℕ) := by
          exact Eq.symm (pow_succ' g ↑i)
        have h_mul : ∀ h : G, g (h y) = (g * h) y := by
          exact fun h => AlgEquiv.congr_fun rfl (h y)
        specialize h_mul (g^(i:ℕ))
        have _ : g ((g^(i:ℕ)) y) = (g^((i+1):ℕ)) y := by
          simp_all
        simp_all
      simp_all
    have _ : z = ∑ i : Finset.range p, - ((g^((i+1):ℕ)) y) * ((i+1):K) := by
      have _ : p-1 + 1 = p := by
        exact Nat.succ_pred_prime hp
      calc
        z = ∑ i : Finset.range p, -((g^(i:ℕ)) y) * (i:K) := by rfl
        _ = ∑ i ∈ Finset.range p, f i := by
          refine Eq.symm (Finset.sum_subtype (Finset.range p) ?_ f)
          exact fun x => Iff.of_eq rfl
        _ = ∑ i ∈ Finset.range (p-1+1), f i := by
          simp_all
        _ = ∑ i ∈ Finset.range (p-1), f (i+1) + f 0 :=
          Finset.sum_range_succ' f (p-1)
        _ = ∑ i ∈ Finset.range (p-1), f (i+1) := by
          have _ : f 0 = 0 := by
            grind
          simp_all
        _ = ∑ i ∈ Finset.range (p-1), f (i+1) + f (p-1+1) := by
          have _ : f p = 0 := by
            have _ : (p : K) = 0 := by
              exact CharP.cast_eq_zero K p
            (expose_names; exact mul_eq_zero_of_right (-(g ^ p) y) h_4)
          simp_all
        _ = ∑ i ∈ Finset.range (p-1+1), f (i+1) := by
          symm
          apply Finset.sum_range_succ (fun i => f (i+1)) (p-1)
        _ = ∑ i ∈ Finset.range p, f (i+1) := by simp_all
        _ = ∑ i : Finset.range p, f (i+1) := by
          refine Finset.sum_subtype (Finset.range p) ?_ (fun i => f (i+1))
          exact fun x => Iff.of_eq rfl
        _ = ∑ i : Finset.range p, - ((g^((i+1):ℕ)) y) * ((i+1):K) := by
          subst f
          simp
    have _ : ∑ i : Finset.range p, - ((g^((i+1):ℕ)) y) * (i:K) = z + 1 := by
      have _ : ∑ i : Finset.range p, - ((g^((i+1):ℕ)) y) * ( i:K ) =
         ∑ i : Finset.range p, ( - (((g^((i+1):ℕ)) y) * ( (i:K) + 1 )) + (g^((i+1):ℕ)) y)
        := by
        have _ : ∀ i : Finset.range p, ( - (((g^((i+1):ℕ)) y) * ( (i:K) + 1 )) + (g^((i+1):ℕ)) y)
          =  - ((g^((i+1):ℕ)) y) * ( i:K ) := by
          have _ : ∀ i : Finset.range p,  - (((g^((i+1):ℕ)) y) * ( (i:K) + 1 ))
            =  - (((g^((i+1):ℕ)) y) * ( i:K )) - (((g^((i+1):ℕ)) y) * ( 1 )) := by
              intro i
              grind
          have h_sub :  ∀ w : K,  ∀ i : Finset.range p, (- (((g^((i+1):ℕ)) y) * ( (i:K) + 1 ))) + w
            =  (- (((g^((i+1):ℕ)) y) * ( i:K )) - (((g^((i+1):ℕ)) y) * ( 1 ))) + w := by
              intro w i
              (expose_names; exact (add_left_inj w).mpr (h_4 i))
          have _ : ∀ i : Finset.range p, (- (((g^((i+1):ℕ)) y) * ( (i:K) + 1 ))) + ((g^((i+1):ℕ)) y)
            =  (- (((g^((i+1):ℕ)) y) * ( i:K )) - (((g^((i+1):ℕ)) y) * ( 1 ))) + ((g^((i+1):ℕ)) y) := by
              intro i
              specialize h_sub ((g^((i+1):ℕ)) y) i
              simp_all
          have _ : ∀ i : Finset.range p,
            (- (((g^((i+1):ℕ)) y) * ( i:K )) - (((g^((i+1):ℕ)) y) * ( 1 ))) + ((g^((i+1):ℕ)) y)
            = - ((g^((i+1):ℕ)) y) * ( i:K )
            := by
              simp
          simp_all
        grind
      have _ : ∑ i : Finset.range p, ( - (((g^((i+1):ℕ)) y) * ( (i:K) + 1 )) + (g^((i+1):ℕ)) y)
        = ∑ i : Finset.range p, ( - (((g^((i+1):ℕ)) y) * ( (i:K) + 1 )))
        +  ∑ i : Finset.range p, ((g^((i+1):ℕ)) y) := by
        exact Finset.sum_add_distrib
      simp_all
    simp_all
  let b := z^p - z
  have ha : ∃ a : F, (algebraMap F K) a = b := by
    have hb : g b = b := by
      calc
        g b = g (z^p - z) := AlgEquiv.congr_fun rfl b
        _ = (z + 1)^p - (z + 1) := by grind
        _ = z^p + 1 - (z + 1) := ?_
        _ = b := by exact add_sub_add_right_eq_sub (z ^ p) z 1
      have h1 : ∀ x : K, (frobenius K) p x = x^p := by
        exact fun x => frobenius_def p x
      have h2 : ∀ (x y : K), (frobenius K) p (x+y) = (frobenius K) p x + (frobenius K) p y := by
        exact fun x y => RingHom.map_add (frobenius K p) x y
      let h3 := h1
      specialize h1 (z + 1)
      specialize h2 z 1
      specialize h3 z
      grind
    have h_fix : ∀ x : K, g x = x → x ∈ IntermediateField.fixedField (Subgroup.zpowers g) :=
      fixed_field_of_cyclic_subgroup F K g
    specialize h_fix b hb
    simp_all
    refine Set.mem_range.mp ?_
    exact (IsGalois.mem_range_algebraMap_iff_fixed b).mpr h_fix
  obtain ⟨a, ha⟩ := ha
  use a
  use z
  let pol := Polynomial.X ^ p - Polynomial.X - Polynomial.C a
  have h_eval : Polynomial.aeval z pol = 0 := by
    calc
      Polynomial.aeval z pol = Polynomial.aeval z (Polynomial.X ^ p - Polynomial.X - Polynomial.C a) := by rfl
      _ = Polynomial.aeval z ((Polynomial.X : Polynomial F) ^ p)
          - Polynomial.aeval z (Polynomial.X : Polynomial F) - Polynomial.aeval z (Polynomial.C a) := by grind
      _ = z^p - z - b := by simp_all
      _ = 0 := by
        subst b
        ring
  have h_gen1 : ∃ g : G, ∀ x, x ∈ Subgroup.zpowers g := by
    apply IsCyclic.exists_generator
  have h_dvd :  minpoly F z ∣ pol ↔ (Polynomial.aeval z) pol = 0 :=
    minpoly.dvd_iff
  have _ : (minpoly F z).natDegree = p := by
    have _ : (minpoly F z).natDegree ∣ Module.finrank F K := by
      apply minpoly.degree_dvd
      exact Algebra.IsIntegral.isIntegral z
    have h2 : ¬ (minpoly F z).natDegree = 1 := by
      by_contra
      have h_tmp1 : z ∈ (algebraMap F K).range := by
        exact minpoly.natDegree_eq_one_iff.mp this
      have hy : ∃ y : F, (algebraMap F K) y = z := by
        exact Set.mem_range.mp h_tmp1
      have hgal : ∀ x : K, x ∈ Set.range (algebraMap F K) ↔ ∀ (g : Gal(K/F)), g x = x :=
        IsGalois.mem_range_algebraMap_iff_fixed
      specialize hgal z
      obtain ⟨hgal1, hgal2⟩ := hgal
      have h_gz : ∀ (g : Gal(K/F)), g z = z := by
        specialize hgal1 h_tmp1
        exact hgal1
      specialize h_gz g
      have _ : z + 1 = z :=
        calc
          z + 1 = g z := by
            symm
            exact hz
          _ = z := h_gz
      simp_all
    have h1 : (minpoly F z).natDegree = 1 ∨ (minpoly F z).natDegree = p := by
      refine (Nat.dvd_prime hp).mp ?_
      (expose_names;
        exact
          (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod hrank) (Module.finrank F K)) h_2).mp h_2)
    simp_all
  have _ : ((Polynomial.X : Polynomial F) ^ p).degree = p :=
    Polynomial.degree_X_pow p
  have _ : ((Polynomial.X : Polynomial F) ^ p).natDegree = p :=
    Polynomial.natDegree_X_pow p
  have _ : ((Polynomial.X : Polynomial F) ^ p).natDegree = ((Polynomial.X : Polynomial F) ^ p - (Polynomial.X : Polynomial F)).natDegree := by
    refine Eq.symm (Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_)
    simp_all
    exact Nat.Prime.one_lt hp
  have _ : (Polynomial.X + Polynomial.C a).degree = 1 :=
   Polynomial.degree_X_add_C a
  have _ : (Polynomial.X + Polynomial.C a).natDegree = 1 :=
    Polynomial.natDegree_X_add_C a
  have h_mon : pol.Monic := by
    have h1 : ((Polynomial.X : Polynomial F) ^ p).Monic :=
      Polynomial.monic_X_pow p
    have _ : (Polynomial.X + Polynomial.C a).degree = 1 :=
      Polynomial.degree_X_add_C a
    have hpol : ((Polynomial.X)^p - (Polynomial.X + Polynomial.C a)).Monic := by
      refine Polynomial.Monic.sub_of_left h1 ?_
      simp
      exact Nat.Prime.one_lt hp
    have h3 : ∀ (x y z : Polynomial F), (x - (y+z)).Monic ↔ (x-y-z).Monic := by
      intro x y z
      ring_nf
    specialize h3 ((Polynomial.X : Polynomial F)^p) (Polynomial.X : Polynomial F) (Polynomial.C a)
    obtain ⟨h3a, h3b⟩ := h3
    specialize h3a hpol
    subst pol
    exact h3a
  have _ : (pol/ₘ (minpoly F z)).natDegree = pol.natDegree - (minpoly F z).natDegree := by
    apply Polynomial.natDegree_divByMonic
    refine minpoly.monic ?_
    exact Algebra.IsIntegral.isIntegral z
  apply monic_divisor_of_same_degree
  refine minpoly.monic ?_
  exact Algebra.IsIntegral.isIntegral z
  apply h_mon
  obtain ⟨h_dvd1, h_dvd2⟩ := h_dvd
  specialize h_dvd2 h_eval
  subst pol
  exact h_dvd2
  simp_all

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
