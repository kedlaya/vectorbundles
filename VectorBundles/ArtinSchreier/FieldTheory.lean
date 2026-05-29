module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public import VectorBundles.ArtinSchreier.Polynomials

@[expose] public section

open IntermediateField
open Polynomial

variable (F K : Type) [Field F] [Field K] [Algebra F K]

lemma finite_extension_degree_one :
  Module.finrank F K > 1 → ¬ Function.Surjective (algebraMap F K) := by
  contrapose
  intro h
  have h2 : Module.rank F K ≤ 1 := by
    calc
    Module.rank F K ≤ Module.rank F K + Module.rank F (Algebra.linearMap F K).ker := by
      apply le_add_of_nonneg_right
      exact Cardinal.zero_le (Module.rank F ↥(Algebra.linearMap F K).ker)
    _ = Module.rank F F := (LinearMap.rank_eq_of_surjective h).symm
    _ = 1 := CommSemiring.rank_self F
  push Not
  exact Module.finrank_le_of_rank_le h2

lemma fixed_field_of_cyclic_subgroup [FiniteDimensional F K]
  [IsGalois F K] (g : Gal(K/F)) : ∀ x : K, g x = x →
    x ∈ fixedField (Subgroup.zpowers g) := by
  intro x hg
  have h_pow : ∀ n : ℕ, (g^n) x = x := by
    intro n
    induction n with
    | zero =>
      calc
      (g ^ 0) x = (1 : Gal(K/F)) x := AlgEquiv.congr_fun rfl x
      _ = x := AlgEquiv.one_apply x
    | succ n hyp =>
      calc
      (g ^ (n+1)) x = ((g^n) * g) x := AlgEquiv.congr_fun rfl x
      _ = (g^n) (g x) :=  AlgEquiv.mul_apply (g ^ n) g x
      _ = (g^n) x := AlgEquiv.congr_arg hg
      _ = x := hyp
  have h_sub : ∀ h : Gal(K/F), h ∈ Subgroup.zpowers g → h x = x := by
    intro h h1
    have h2 : ∃ n : ℕ, g ^ n = h := by
      refine (Submonoid.mem_powers_iff h g).mp ?_
      exact mem_powers_iff_mem_zpowers.mpr h1
    obtain ⟨n, h2⟩ := h2
    subst h
    exact h_pow n
  exact (mem_fixedField_iff (Subgroup.zpowers g) x).mpr h_sub

lemma cyclic_char_p_as_artin_schreier {p : ℕ} [FiniteDimensional F K]
  (hp: Nat.Prime p) (hrank: Module.finrank F K = p)
    (hsep: IsGalois F K) (hchar: ringChar F = p) : ∃ (a : F), ∃ (x : K),
      minpoly F x = X ^ p - X - C a := by
  have hy : ∃ (y : K), Algebra.trace F K y = 1 :=
    have h : Function.Surjective (Algebra.trace F K) := Algebra.trace_surjective F K
    Set.mem_range.mp (h 1)
  obtain ⟨y, hy⟩ := hy
  have : CharP K p :=
    have h : CharP F p := ringChar.of_eq hchar
    (Algebra.charP_iff F K p).mp h
  have : ExpChar K p := ExpChar.prime hp
  let G := Gal(K/F)
  have h_ord : Nat.card G = p := by
    calc
    Nat.card G = Module.finrank F K := IsGalois.card_aut_eq_finrank F K
    _  = p := hrank
  have : Fact (Nat.Prime p) := fact_iff.mpr hp
  have : IsCyclic G := isCyclic_of_prime_card h_ord
  have h_gen : ∃ g : G, Subgroup.zpowers g = ⊤ := isCyclic_iff_exists_zpowers_eq_top.mp this
  obtain ⟨g, h_gen⟩ := h_gen
  have h_ordg : orderOf g = p := by
    calc
    orderOf g = Nat.card G := orderOf_eq_card_of_zpowers_eq_top h_gen
    _ = p := h_ord
  let f (i : ℕ) : K := -(g^i) y * i
  let z := ∑ i : Finset.range p, -((g^(i:ℕ)) y) * (i:K)
  have hz : g z = z + 1 := by
    have : ∑ i : Finset.range p, (g^((i+1):ℕ)) y = 1 := by
      have h_trace_as_sum : algebraMap F K (Algebra.trace F K y) = ∑ σ : Gal(K/F), σ y :=
        trace_eq_sum_automorphisms y
      let f : Finset.range p → Gal(K/F) := fun i => g ^((i+1):ℕ)
      have _ : Function.Bijective f := by
        apply (Nat.bijective_iff_injective_and_card f).mpr
        constructor
        · by_contra
          unfold Function.Injective at this
          push Not at this
          obtain ⟨i1, hi1⟩ := this
          obtain ⟨i2, hi2, hi3⟩ := hi1
          have h_po : g^((i1+1):ℤ) = g^((i2+1):ℤ) :=
            AlgEquiv.ext_iff.mpr (congrFun (congrArg DFunLike.coe hi2))
          let j := (i1 : ℤ) - (i2 : ℤ)
          have h_pj: (p : ℤ) ∣ j := by
            have h : (orderOf g : ℤ) ∣ ((i1+1):ℤ) - ((i2+1):ℤ) :=
              orderOf_dvd_sub_iff_zpow_eq_zpow.mpr h_po
            subst j
            simp_all
          have h_e : ∃ e : ℤ, j = e * p := (dvd_iff_exists_eq_mul_left).mp h_pj
          obtain ⟨e, h_e⟩ := h_e
          have h_e2 : e ≥ 1 ∨ e ≤ -1 := by grind
          cases h_e2 with
          | inl h =>
            have : e * p ≥ 1 * p := by
              refine Int.mul_le_mul_of_nonneg_right h ?_
              exact Int.natCast_nonneg p
            grind
          | inr h =>
            have : e * p ≤ -1 * p := by
              refine Int.mul_le_mul_of_nonneg_right h ?_
              exact Int.natCast_nonneg p
            grind
        · calc
          Nat.card ↥(Finset.range p) = p := by
            calc
              Nat.card ↥(Finset.range p) = Finset.card (Finset.range p) :=
                Nat.card_eq_finsetCard (Finset.range p)
              _ = p := Finset.card_range p
          _ = Nat.card G := h_ord.symm
      have h_trace_as_sum2 : ∑ i : Finset.range p, (g^((i+1):ℕ)) y = ∑ σ : Gal(K/F), σ y := by
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
    have : g z = ∑ i : Finset.range p, - ((g^((i+1):ℕ)) y) * (i:K) := by
      calc
        g z = ∑ i : Finset.range p, -g (((g^(i:ℕ)) y) * (i:K)) := by
          have : g (∑ i : Finset.range p, ((g^(i:ℕ)) y) * (i:K)) =
            ∑ i : Finset.range p, g (((g^(i:ℕ)) y) * (i:K)) := by apply map_finset_sum
          subst z
          simp_all
        _ = ∑ i : Finset.range p, - ((g^((i+1):ℕ)) y) * (i:K) := by
          have h : ∀ i : Finset.range p, g (((g^(i:ℕ)) y) * (i:K)) = ((g^((i+1):ℕ)) y) * (i:K) := by
            intro i
            calc
            g (((g^(i:ℕ)) y) * (i:K)) = g ((g^(i:ℕ)) y) * (i:K) := by
              subst hrank
              aesop
            _ = ((g^((i+1):ℕ)) y) * (i:K) := by
              have : g ((g^(i:ℕ)) y) = (g^((i+1):ℕ)) y := by
                calc
                g ((g^(i:ℕ)) y) = (g * (g^(i:ℕ))) y := AlgEquiv.congr_fun rfl ((g^(i:ℕ)) y)
                _ =  (g^((i+1):ℕ)) y := by rw [pow_succ' g ↑i]
              rw [this]
          apply Finset.sum_congr
          · simp
          · intro x a
            aesop
    have : z = ∑ i : Finset.range p, - (g^((i+1):ℕ)) y * ((i+1):K) := by
      have : p-1 + 1 = p := Nat.succ_pred_prime hp
      calc
        z = ∑ i ∈ Finset.range p, f i := by
          refine (Finset.sum_subtype (Finset.range p) ?_ f).symm
          exact fun x => Iff.of_eq rfl
        _ = ∑ i ∈ Finset.range (p-1+1), f i :=
          Finset.sum_congr (congrArg Finset.range this.symm) fun x => congrFun rfl
        _ = ∑ i ∈ Finset.range (p-1), f (i+1) + f 0 :=
          Finset.sum_range_succ' f (p-1)
        _ = ∑ i ∈ Finset.range (p-1), f (i+1) :=
          have h: f 0 = 0 := by
            refine mul_eq_zero_of_right (-(g ^ 0) y) ?_
            exact AddMonoidWithOne.natCast_zero
          add_eq_left.mpr h
        _ = ∑ i ∈ Finset.range (p-1), f (i+1) + f (p-1+1) := by
          have _ : f p = 0 :=
            have h : (p : K) = 0 := CharP.cast_eq_zero K p
            mul_eq_zero_of_right (-(g ^ p) y) h
          simp_all
        _ = ∑ i ∈ Finset.range (p-1+1), f (i+1) :=
          (Finset.sum_range_succ (fun i => f (i+1)) (p-1)).symm
        _ = ∑ i ∈ Finset.range p, f (i+1) := by simp_all
        _ = ∑ i : Finset.range p, f (i+1) := by
          refine Finset.sum_subtype (Finset.range p) ?_ (fun i => f (i+1))
          exact fun x => Iff.of_eq rfl
        _ = ∑ i : Finset.range p, - (g^((i+1):ℕ)) y * ((i+1):K) := by
          subst f
          simp
    have : ∑ i : Finset.range p, - (g^((i+1):ℕ)) y * (i:K) = z + 1 := by
      have : ∑ i : Finset.range p, - (g^((i+1):ℕ)) y * (i:K) =
        ∑ i : Finset.range p, (- (((g^((i+1):ℕ)) y) * ((i:K) + 1)) + (g^((i+1):ℕ)) y) := by
        have _ : ∀ i : Finset.range p, ( - (((g^((i+1):ℕ)) y) * ( (i:K) + 1 )) + (g^((i+1):ℕ)) y)
          =  - ((g^((i+1):ℕ)) y) * ( i:K ) := by
          intro i
          have h : - (((g^((i+1):ℕ)) y) * ((i:K) + 1))
            =  - (((g^((i+1):ℕ)) y) * (i:K)) - (((g^((i+1):ℕ)) y) * 1) := by grind
          have :  (- (((g^((i+1):ℕ)) y) * ((i:K) + 1))) + ((g^((i+1):ℕ)) y)
            =  (- (((g^((i+1):ℕ)) y) * (i:K)) - (((g^((i+1):ℕ)) y) * 1)) + ((g^((i+1):ℕ)) y) :=
            (add_left_inj ((g^((i+1):ℕ)) y)).mpr h
          have _ : (- (((g^((i+1):ℕ)) y) * (i:K)) - (((g^((i+1):ℕ)) y) * 1)) + ((g^((i+1):ℕ)) y)
            = - ((g^((i+1):ℕ)) y) * (i:K) := by simp
          simp_all
        grind
      have : ∑ i : Finset.range p, ( - (((g^((i+1):ℕ)) y) * ( (i:K) + 1 )) + (g^((i+1):ℕ)) y)
        = ∑ i : Finset.range p,  - ((g^((i+1):ℕ)) y * ( (i:K) + 1 ))
        +  ∑ i : Finset.range p, (g^((i+1):ℕ)) y := Finset.sum_add_distrib
      simp_all
    simp_all
  have ha : ∃ a : F, (algebraMap F K) a = z^p - z := by
    let b := z^p - z
    have hb : g b = b := by
      calc
        g b = g (z^p - z) := AlgEquiv.congr_fun rfl b
        _ = (z + 1)^p - (z + 1) := by grind
        _ = z^p + 1^p - (z + 1) := sub_left_inj.mpr (add_pow_char z 1 p)
        _ = z^p + 1 - (z + 1) := by simp
        _ = b := add_sub_add_right_eq_sub (z ^ p) z 1
    have : b ∈ fixedField (Subgroup.zpowers g) :=
      fixed_field_of_cyclic_subgroup F K g b hb
    aesop
  obtain ⟨a, ha⟩ := ha
  use a, z
  let pol := X ^ p - X - C a
  have h_pol : pol.natDegree = p ∧ pol.Monic := artin_schreier_poly a hp
  obtain ⟨h_pdeg, h_mon⟩ := h_pol
  have h_eval : aeval z pol = 0 := by
    calc
      aeval z pol = aeval z ((X : Polynomial F) ^ p) - aeval z (X : Polynomial F) - aeval z (C a) := by grind
      _ = 0 := by simp_all
  have h_gen1 : ∃ g : G, ∀ x, x ∈ Subgroup.zpowers g := IsCyclic.exists_generator
  have h_int: IsIntegral F z := Algebra.IsIntegral.isIntegral z
  have h_mpdeg : (minpoly F z).natDegree = p := by
    have h : (minpoly F z).natDegree ∣ Module.finrank F K := minpoly.degree_dvd h_int
    have h1 : (minpoly F z).natDegree = 1 ∨ (minpoly F z).natDegree = p := by
      refine (Nat.dvd_prime hp).mp ?_
      exact (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod hrank) (Module.finrank F K)) h).mp h
    by_contra
    have : (minpoly F z).natDegree = 1 := by aesop
    have h_tmp1 : z ∈ (algebraMap F K).range := minpoly.natDegree_eq_one_iff.mp this
    have h_gz : ∀ (g : Gal(K/F)), g z = z := (IsGalois.mem_range_algebraMap_iff_fixed z).mp h_tmp1
    simp_all
  apply monic_divisor_of_same_degree
  · exact minpoly.monic h_int
  · apply h_mon
  · exact minpoly.dvd_iff.mpr h_eval
  · rw [h_mpdeg]
    exact h_pdeg.symm

lemma nonsquare_in_quadratic_extension [FiniteDimensional F K]
  (hrank: Module.finrank F K = 2) (hchar: ringChar F ≠ 2) :
    ∃ a : F, ¬ IsSquare a := by
  have h_char : ringChar F = ringChar K := Algebra.ringChar_eq F K
  have : CharP F (ringChar K) := ringChar.of_eq h_char
  have prim : (primitiveRoots (Module.finrank F K) F).Nonempty := by
    unfold primitiveRoots
    refine Finset.nonempty_def.mpr ?_
    use -1
    simp only [Finset.mem_filter, Multiset.mem_toFinset]
    constructor
    · simp_all
    · rw [hrank]
      refine IsPrimitiveRoot.neg_one (ringChar K) ?_
      rw [← h_char]
      apply hchar
  have hsep : Algebra.IsSeparable F K := by
    let d := Field.finInsepDegree F K
    let e := Field.finSepDegree F K
    have h_de_prod : e * d = 2 := by
      calc
        e * d = Module.finrank F K := Field.finSepDegree_mul_finInsepDegree F K
        _ = 2 := hrank
    refine (Field.finSepDegree_eq_finrank_iff F K).mp ?_
    rw [hrank]
    have hd : d = 1 ∨ d = 2 :=
      have hd : d ∣ 2 := dvd_of_mul_left_eq e h_de_prod
      (Nat.dvd_prime Nat.prime_two).mp hd
    let q := ringExpChar F
    have hf : ∃ f : ℕ, d = q^f := finInsepDegree_eq_pow F K q
    obtain ⟨f, hf⟩ := hf
    by_contra
    have hf1 : f ≥ 1 := by
      by_contra
      push Not at this
      aesop
    have _ : q = 2 := by
      have _ : q = 1 ∨ q = 2 :=
        have h_q2 : q ∣ 2 := by
          have _ : q^1 ∣ q^f := Nat.pow_dvd_pow q hf1
          grind
        (Nat.dvd_prime (Nat.prime_two)).mp h_q2
      have _ : q ≠ 1 := by
        by_contra
        have _ : q ^ f = 1 := by
          refine Nat.pow_eq_one.mpr ?_
          left
          exact this
        grind
      grind
    have h_chars : ∀ (p q : ℕ) [hp : CharP F p] [hq : ExpChar F q], p = q ↔ Nat.Prime p :=
      char_eq_expChar_iff F
    specialize h_chars (ringChar K) q
    have h_chars2 : ∀ (p q : ℕ) [CharP F p] [ExpChar F q], q = 1 ↔ p = 0 :=
      expChar_one_iff_char_zero F
    specialize h_chars2 (ringChar K) q
    have h_chars3 : ∀ (p : ℕ) [hc : CharP F p], Nat.Prime p ∨ p = 0 :=
      CharP.char_is_prime_or_zero F
    grind
  have hb : ∃ (b : K), b ^ Module.finrank F K ∈ Set.range (algebraMap F K) ∧ F⟮b⟯ = (⊤: IntermediateField F K) :=
    have : Algebra.IsQuadraticExtension F K :=
      { toFree := Module.free_of_finite_type_torsion_free', finrank_eq_two' := hrank }
    have : IsCyclic Gal(K/F) := Algebra.IsQuadraticExtension.isCyclic F K
    exists_root_adjoin_eq_top_of_isCyclic F K prim
  obtain ⟨b, hb1, hb2⟩ := hb
  have ha : ∃ (a : F), b ^ 2 = (algebraMap F K) a := by
    simp_all only [ne_eq, Set.mem_range, adjoin_eq_top_iff]
    obtain ⟨a, hb1⟩ := hb1
    use a
    symm
    exact hb1
  obtain ⟨a, ha⟩ := ha
  use a
  by_contra
  unfold IsSquare at this
  obtain ⟨c, this⟩ := this
  have hb3 : (algebraMap F K) c = b ∨ (algebraMap F K) (-c) = b := by grind
  have hb4 : b ∈ (algebraMap F K).range := by
    refine RingHom.mem_range.mpr ?_
    cases hb3
    · use c
    · use -c
  have : Module.finrank F K = 1 :=
    have h : F⟮b⟯ = (⊥: IntermediateField F K) := adjoin_simple_eq_bot_iff.mpr hb4
    have h1 : (⊥: IntermediateField F K) = (⊤: IntermediateField F K) := by
      rw [h] at hb2
      exact hb2
    bot_eq_top_iff_finrank_eq_one.mp h1
  simp_all

lemma trivial_absolute_galois_group [Algebra.IsSeparable F K] [IsAlgClosure F K]
    [FiniteDimensional F K] (h : Nat.card Gal(K/F) = 1) : IsAlgClosed F := by
  have : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_3, to_normal := IsAlgClosure.normal F K })
  have h_rank : Module.finrank F K = 1 := by
    calc
    Module.finrank F K = Nat.card Gal(K/F) := (IsGaloisGroup.card_eq_finrank Gal(K/F) F K).symm
    _ = 1 := h
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  let iota := algebraMap F K
  have h_range: ∀ (b : K), b ∈ iota.range := by
    intro b
    have h : (⊥ : IntermediateField F K) = (⊤ : IntermediateField F K) :=
      IntermediateField.bot_eq_top_iff_finrank_eq_one.mpr h_rank
    have : b ∈ (⊥ : IntermediateField F K) := by simp_all
    exact RingHom.mem_range.mpr this
  refine IsAlgClosed.of_exists_root F ?_
  intro p h1 h2
  have hb: ∃ (b : K), aeval b p = 0 := by
    refine IsAlgClosed.exists_aeval_eq_zero K p ?_
    have h_2 : 0 < degree p := Irreducible.degree_pos h2
    exact (Std.ne_of_lt h_2).symm
  obtain ⟨b, hb⟩ := hb
  have ha : ∃ (a : F), iota a = b :=
    Set.mem_range.mp (h_range b)
  obtain ⟨a, ha⟩ := ha
  use a
  have _ : iota (eval a p) = eval (iota a) (p.map iota) :=
    (eval_map_apply (algebraMap F K) a).symm
  subst iota
  simp_all
