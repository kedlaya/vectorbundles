module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public import VectorBundles.ArtinSchreier.Polynomials

@[expose] public section

open IntermediateField
open Module
open Polynomial

variable (F K : Type) [Field F] [Field K] [Algebra F K]

lemma finite_extension_degree_one : finrank F K > 1 → ¬ Function.Surjective (algebraMap F K) := by
  contrapose
  intro h
  push Not
  apply finrank_le_of_rank_le
  calc
  Module.rank F K ≤ Module.rank F K + Module.rank F (Algebra.linearMap F K).ker := by
    apply le_add_of_nonneg_right
    exact Cardinal.zero_le (Module.rank F ↥(Algebra.linearMap F K).ker)
  _ = Module.rank F F := (LinearMap.rank_eq_of_surjective h).symm
  _ = 1 := CommSemiring.rank_self F

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
  (hp: Nat.Prime p) (hrank: finrank F K = p)
    (hsep: IsGalois F K) (hchar: ringChar F = p) : ∃ (a : F), ∃ (x : K),
      minpoly F x = X ^ p - X - C a := by
  have hy : ∃ (y : K), Algebra.trace F K y = 1 :=
    Set.mem_range.mp (Algebra.trace_surjective F K 1)
  obtain ⟨y, hy⟩ := hy
  have : CharP K p := (Algebra.charP_iff F K p).mp (ringChar.of_eq hchar)
  let G := Gal(K/F)
  have h_ord : Nat.card G = p := by
    calc
    Nat.card G = finrank F K := IsGalois.card_aut_eq_finrank F K
    _  = p := hrank
  have : Fact (Nat.Prime p) := fact_iff.mpr hp
  have : IsCyclic G := isCyclic_of_prime_card h_ord
  have h_gen : ∃ g : G, Subgroup.zpowers g = ⊤ := isCyclic_iff_exists_zpowers_eq_top.mp this
  obtain ⟨g, h_gen⟩ := h_gen
  have h_ordg : orderOf g = p := by
    calc
    orderOf g = Nat.card G := orderOf_eq_card_of_zpowers_eq_top h_gen
    _ = p := h_ord
  let z := ∑ i : Finset.range p, ((g^(i:ℕ)) y) * (i:K)
  have : g z = z - 1 := by
    let f (i : ℕ) : K := (g^i) y * i
    calc
    g z = g (∑ i : Finset.range p, ((g^(i:ℕ)) y) * (i:K) ) := by rfl
    _ = ∑ i : Finset.range p, g (((g^(i:ℕ)) y) * (i:K)) := by apply map_finset_sum
    _ = ∑ i : Finset.range p, ( ((g^((i+1):ℕ)) y) * ((i:K) + 1) - (g^((i+1):ℕ)) y) := by
      have h : ∀ i : Finset.range p, g (((g^(i:ℕ)) y) * (i:K)) =
        ( ((g^((i+1):ℕ)) y) * ( (i:K) + 1 ) - (g^((i+1):ℕ)) y) := by
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
        _ = ( ((g^((i+1):ℕ)) y) * ( (i:K) + 1 ) - (g^((i+1):ℕ)) y) := by grind
      apply Finset.sum_congr rfl
      intro x a
      apply h
    _ = ∑ i : Finset.range p, ( ((g^((i+1):ℕ)) y) * ((i:K) + 1)) -
      ∑ i : Finset.range p, (g^((i+1):ℕ)) y := by apply Finset.sum_sub_distrib
    _ = z - 1 := by
      have h1 : z = ∑ i : Finset.range p, (g^((i+1):ℕ)) y * ((i+1):K) := by
        have hp1 : p-1 + 1 = p := Nat.succ_pred_prime hp
        calc
          z = ∑ i ∈ Finset.range p, f i := by
            refine (Finset.sum_subtype (Finset.range p) ?_ f).symm
            exact fun x => Iff.of_eq rfl
          _ = ∑ i ∈ Finset.range (p-1+1), f i := by rw [hp1]
          _ = ∑ i ∈ Finset.range (p-1), f (i+1) + f 0 := Finset.sum_range_succ' f (p-1)
          _ = ∑ i ∈ Finset.range (p-1), f (i+1) := by aesop
          _ = ∑ i ∈ Finset.range (p-1), f (i+1) + f (p-1+1) := by aesop
          _ = ∑ i ∈ Finset.range (p-1+1), f (i+1) :=
            (Finset.sum_range_succ (fun i => f (i+1)) (p-1)).symm
          _ = ∑ i ∈ Finset.range p, f (i+1) := by rw [hp1]
          _ = ∑ i : Finset.range p, f (i+1) := by
            refine Finset.sum_subtype (Finset.range p) ?_ (fun i => f (i+1))
            exact fun x => Iff.of_eq rfl
          _ = ∑ i : Finset.range p, (g^((i+1):ℕ)) y * ((i+1):K) := by simp [f]
      have h2 : ∑ i : Finset.range p, (g^((i+1):ℕ)) y = 1 := by
        calc
        ∑ i : Finset.range p, (g^((i+1):ℕ)) y = ∑ σ : Gal(K/F), σ y := by
          let f : Finset.range p → Gal(K/F) := fun i => g ^ ((i+1):ℕ)
          have h_bij: Function.Bijective f := by
            apply (Nat.bijective_iff_surjective_and_card f).mpr
            constructor
            · intro b
              have : DecidableEq G := Classical.typeDecidableEq G
              have hb1 : g ^ (-1:ℤ) * b ∈ Finset.image (fun x => g ^ x) (Finset.range (orderOf g)) := by
                have hb : g ^ (-1:ℤ) * b ∈ Subgroup.zpowers g := by simp_all only [Subgroup.mem_top]
                refine (IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf ?_).mp hb
                exact isOfFinOrder_of_finite g
              simp_all only [Finset.mem_image, Subtype.exists]
              obtain ⟨i, hb1, hb2⟩ := hb1
              use i, hb1
              calc
                g ^ ((i+1):ℕ) = g * (g ^ (i:ℕ)) := pow_succ' g i
                _ = g * (g ^ (-1:ℤ) * b) := by rw [hb2]
                _ = g * g ^ (-1:ℤ) * b := (Semigroup.mul_assoc g (g ^ (-1)) b).symm
                _ = b := by simp
            · calc
              Nat.card ↥(Finset.range p) = p := by
                calc
                  Nat.card ↥(Finset.range p) = Finset.card (Finset.range p) :=
                    Nat.card_eq_finsetCard (Finset.range p)
                  _ = p := Finset.card_range p
              _ = Nat.card G := h_ord.symm
          apply Finset.sum_bijective f h_bij
          · aesop
          · intro i hi
            subst f
            simp
        _ = algebraMap F K (Algebra.trace F K y) := (trace_eq_sum_automorphisms y).symm
        _ = algebraMap F K 1 := by rw [hy]
        _ = 1 := algebraMap.coe_one
      rw [h1, h2]
  have ha : ∃ a : F, (algebraMap F K) a = z^p - z := by
    let b := z^p - z
    have hb : g b = b := by
      calc
        g b = g (z^p - z) := AlgEquiv.congr_fun rfl b
        _ = g (z^p) - g z := map_sub g (z ^ p) z
        _ = (g z) ^ p - g z := sub_left_inj.mpr (map_pow g z p)
        _ = (z - 1)^p - (z - 1) := by rw [this]
        _ = z^p - 1^p - (z - 1) := sub_left_inj.mpr (sub_pow_char z 1)
        _ = z^p - 1 - (z - 1) := by simp
        _ = b := sub_sub_sub_cancel_right (z ^ p) z 1
    have : b ∈ fixedField (Subgroup.zpowers g) := fixed_field_of_cyclic_subgroup F K g b hb
    aesop
  obtain ⟨a, ha⟩ := ha
  use a, z
  let pol := X ^ p - X - C a
  have h_pol : pol.natDegree = p ∧ pol.Monic := artin_schreier_poly a hp
  obtain ⟨h_pdeg, h_mon⟩ := h_pol
  have h_eval : aeval z pol = 0 := by aesop
  have h_int: IsIntegral F z := Algebra.IsIntegral.isIntegral z
  have h_mpdeg : (minpoly F z).natDegree = p := by
    have h : (minpoly F z).natDegree ∣ finrank F K := minpoly.degree_dvd h_int
    have h1 : (minpoly F z).natDegree = 1 ∨ (minpoly F z).natDegree = p := by
      refine (Nat.dvd_prime hp).mp ?_
      exact (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod hrank) (finrank F K)) h).mp h
    by_contra
    have : (minpoly F z).natDegree = 1 := by aesop
    have h_tmp1 : z ∈ (algebraMap F K).range := minpoly.natDegree_eq_one_iff.mp this
    have h_gz : ∀ (g : Gal(K/F)), g z = z := (IsGalois.mem_range_algebraMap_iff_fixed z).mp h_tmp1
    grind
  apply monic_divisor_of_same_degree
  · exact minpoly.monic h_int
  · apply h_mon
  · exact minpoly.dvd_iff.mpr h_eval
  · rw [h_mpdeg]
    exact h_pdeg.symm

lemma nonsquare_in_quadratic_extension [FiniteDimensional F K]
  (hrank: finrank F K = 2) (hchar: ringChar F ≠ 2) :
    ∃ a : F, ¬ IsSquare a := by
  have h_char : ringChar F = ringChar K := Algebra.ringChar_eq F K
  have : CharP F (ringChar K) := ringChar.of_eq h_char
  have prim : (primitiveRoots (finrank F K) F).Nonempty := by
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
        e * d = finrank F K := Field.finSepDegree_mul_finInsepDegree F K
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
  have hb : ∃ (b : K), b ^ finrank F K ∈ Set.range (algebraMap F K) ∧ F⟮b⟯ = (⊤: IntermediateField F K) :=
    have : Algebra.IsQuadraticExtension F K :=
      { toFree := free_of_finite_type_torsion_free', finrank_eq_two' := hrank }
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
  have : finrank F K = 1 :=
    have h : F⟮b⟯ = (⊥: IntermediateField F K) := adjoin_simple_eq_bot_iff.mpr hb4
    have h1 : (⊥: IntermediateField F K) = (⊤: IntermediateField F K) := by
      rw [h] at hb2
      exact hb2
    bot_eq_top_iff_finrank_eq_one.mp h1
  simp_all
