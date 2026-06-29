module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

open Polynomial

@[simp]
lemma artinSchreierPoly_isMonicOfDegree {F : Type} [Field F] {p : ℕ} (a : F) (hp : 1 < p) :
    (X ^ p - X - C a).IsMonicOfDegree p := by
  rw [←natDegree_X_add_C a] at hp; rw [←sub_add_eq_sub_sub]
  exact IsMonicOfDegree.sub (isMonicOfDegree_X_pow F p) hp

@[simp]
lemma artinSchreierPoly_taylor (F : Type) [Field F] {p : ℕ} [CharP F p] (a c : F)
    (hp : Nat.Prime p) : (X ^ p - X - C a).taylor c = X^p - X + C (c^p - c - a) := by
  have := fact_iff.mpr hp; calc
  (X ^ p - X - C a).taylor c = (X + C c)^p - (X + C c) - C a := by simp
  _ = X^p - X + C (c^p - c - a) := by grind [add_pow_char]

lemma artinSchreierPoly_isRoot_splits (F : Type) [Field F] {p : ℕ} [CharP F p] (a : F)
    (hp : Nat.Prime p) (hr : (X ^ p - X - C a).roots ≠ 0) : Splits (X ^ p - X - C a) := by
  have := fact_iff.mpr hp; have ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hr
  have := Subfield.fintypeBot F p; have := Splits.map (Subfield.splits_bot F p) (algebraMap _ F)
  have : ((X ^ p - X - C a).taylor c).Splits := by simp_all
  exact (splits_iff_comp_splits_of_natDegree_eq_one (natDegree_X_add_C c)).mpr this

lemma artinSchreierPoly_irred (F : Type) [Field F] {p : ℕ} [CharP F p] (a : F)
  (hp : Nat.Prime p) (hr : (X ^ p - X - C a).roots = 0) : Irreducible (X ^ p - X - C a) := by
  open AdjoinRoot Multiset Nat UniqueFactorizationMonoid in
  have hp0 := Nat.Prime.pos hp; let pol := (X ^ p - X - C a); let S := factors pol
  have hmon := artinSchreierPoly_isMonicOfDegree a (Prime.one_lt hp)
  have h0 := IsMonicOfDegree.ne_zero hmon
  have hirr : ∀ b ∈ S, Irreducible b := irreducible_of_factor
  have hirr1 := fun b a ↦ Irreducible.natDegree_pos (hirr b a)
  have hirr2 : ∀ b ∈ S, b ∣ pol := fun b a ↦ dvd_of_mem_factors a
  have hirr3 := fun b a ↦ ne_zero_of_natDegree_gt (hirr1 b a)
  have ⟨b, hb⟩ : ∃ b, b ∈ S := by
    rw [←hmon.1] at hp0; exact exists_mem_factors h0 (not_isUnit_of_natDegree_pos pol hp0)
  have hbc : ∀ c, c ∈ S → b.natDegree ∣ c.natDegree := by
    intro c hc; have := fact_iff.mpr (irreducible_mul_leadingCoeff_inv.mpr (hirr c hc))
    let K := AdjoinRoot (c * C c.leadingCoeff⁻¹); let iota := algebraMap F K
    have hm1 := AdjoinRoot.isAdjoinRootMonic _ (monic_mul_leadingCoeff_inv (hirr3 c hc))
    have := (Algebra.charP_iff F K p).mp ‹CharP F p›
    have hroot1 := IsRoot.dvd (isRoot_root _) (map_dvd iota (y := pol) (by aesop))
    let pol' := pol.map iota; have hr : pol'.IsRoot ≠ ⊥ := by
      apply ne_of_not_le; exact Not.intro fun a => a (root _) hroot1
    have hdiv : b.map iota ∣ pol' := map_dvd iota (hirr2 b hb)
    have hmap : pol' = X^p - X - C (iota a) := by aesop
    have hmap0 : pol' ≠ 0 := map_ne_zero h0; rw [hmap] at hmap0 hdiv hr
    have h := (roots_eq_zero_iff_isRoot_eq_bot hmap0).mp.mt hr
    have hsp1 := artinSchreierPoly_isRoot_splits K _ hp h
    have hd := Irreducible.natDegree_dvd_finrank (hirr b hb) (Splits.of_dvd hsp1 hmap0 hdiv)
    rw [IsAdjoinRootMonic.finrank hm1, natDegree_mul_leadingCoeff_self_inv c] at hd; exact hd
  have hnd := fun f n (h : 0 < n) ↦ degree_eq_iff_natDegree_eq_of_pos h (R := F) (p := f)
  have : b.natDegree = 1 ∨ b.natDegree = p := by
    have htd : ∀ t, t ∈ S.map natDegree → b.natDegree ∣ t := by
      intro _ ht; have ⟨c, hc1, hc2⟩ := mem_map.mp ht; rw [←hc2]; exact hbc c hc1
    have hd := degree_eq_degree_of_associated (factors_prod h0)
    rw [(hnd _ _ hp0).mpr hmon.1] at hd; have hdiv := dvd_sum htd
    rw [←natDegree_multiset_prod S (by aesop), (hnd _ _ hp0).mp hd] at hdiv
    exact Prime.eq_one_or_self_of_dvd hp b.natDegree hdiv
  rcases this with h | h
  · have ⟨x, hx⟩ := exists_root_of_degree_eq_one ((hnd _ _ one_pos).mpr h)
    have hroot := (mem_roots h0).mpr (IsRoot.dvd hx (hirr2 b hb)); aesop
  · have := associated_of_dvd_of_natDegree_le (hirr2 b hb) h0
    rw [hmon.1, h] at this; exact Associated.irreducible (this (le_refl p)) (hirr b hb)

lemma artinSchreierPoly_irred_or_splits (F : Type) [Field F] {p : ℕ} [CharP F p] (a : F)
  (hp : Nat.Prime p) : Irreducible (X ^ p - X - C a) ∨ Splits (X ^ p - X - C a) := by
  by_cases hr : (X ^ p - X - C a).roots = 0
  · left; exact artinSchreierPoly_irred F a hp hr
  · right; exact artinSchreierPoly_isRoot_splits F a hp hr

lemma cyclic_char_p_as_param (F K : Type) [Field F] [Field K] [Algebra F K]
    [IsGalois F K] {p : ℕ} [CharP F p] (hp: Nat.Prime p) (hrank: Module.finrank F K = p) :
    ∃ a : F, ∃ z : K, minpoly F z = X ^ p - X - C a := by
  open Algebra Finset IsGalois MulAction Subgroup Nat minpoly in
  have := FiniteDimensional.of_finrank_pos (by rw [hrank]; exact Prime.pos hp)
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  let G := Gal(K/F); have h_ord := card_aut_eq_finrank F K; rw [hrank] at h_ord
  have := fact_iff.mpr hp; have := isCyclic_of_prime_card h_ord
  have ⟨g, h_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp this
  have h_ordg := orderOf_eq_card_of_zpowers_eq_top h_gen; rw [h_ord] at h_ordg
  have ⟨y, hy⟩ := trace_surjective F K 1; let rp := range p; let z := ∑ i : rp, (g^(i:ℕ)) y * i
  have hz1 := by
    have hp1 : p - 1 + 1 = p := succ_pred_prime hp
    let f := fun (i : ℕ) ↦ (g^i) y * i; let f1 := fun i ↦ f (i+1)
    have : ∑ i ∈ range (p-1), f1 i + f (p-1+1) = ∑ i ∈ range (p-1), f1 i + f 0 := by simp_all [f]
    rw [←sum_range_succ f1 (p-1), ←sum_range_succ' f (p-1), hp1] at this
    calc
    ∑ i : rp, (g^(i+1:ℕ)) y * (i+1) = ∑ i : rp, f (i+1) := by simp [f]
    _ = ∑ i ∈ rp, f1 i := (sum_subtype rp (fun _ ↦ Iff.of_eq rfl) f1).symm
    _ = ∑ i ∈ rp, f i := this
    _ = z := sum_subtype rp (fun _ ↦ Iff.of_eq rfl) f
  have hz2 : ∑ i : rp, (g^(i+1:ℕ)) y = ∑ σ : G, σ y := by open IsOfFinOrder in
    let f := fun (i : rp) ↦ g ^ (i+1:ℕ); refine sum_bijective f ?_ (by simp) (fun _ _ ↦ rfl)
    refine (Nat.bijective_iff_surjective_and_card f).mpr ⟨?_, ?_⟩
    · have : DecidableEq G := Classical.typeDecidableEq G
      intro b; have h := mem_top (g ^ (-1:ℤ) * b); rw [←h_gen] at h
      have h := (mem_zpowers_iff_mem_range_orderOf (isOfFinOrder_of_finite g)).mp h
      rw [h_ordg, mem_image] at h; have ⟨i, hb1, hb2⟩ := h; use ⟨i, hb1⟩
      simp only [f, pow_succ' g i, hb2, zpow_neg, zpow_one, mul_inv_cancel_left]
    · rw [card_eq_finsetCard rp, card_range p, ←h_ord]
  have hgz := calc
    g z = ∑ i : rp, g ((g^(i:ℕ)) y * i) := map_finset_sum _ _
    _ = ∑ i : rp, (g^(i+1:ℕ)) y * i := by simp [pow_succ' g]
    _ = ∑ i : rp, ((g^(i+1:ℕ)) y * (i+1) - (g^(i+1:ℕ)) y) := by grind only
    _ = z - 1 := by rw [sum_sub_distrib, hz1, hz2, ←trace_eq_sum_automorphisms, hy, map_one]
  have hz3 : z ∉ (algebraMap F K).range := by
    apply (mem_range_algebraMap_iff_fixed z (E := K)).mp.mt; push Not; use g; grind only
  let b := z^p - z; have ⟨a, _⟩ : b ∈ (⊥ : IntermediateField F K) := by
    apply (mem_bot_iff_fixed b).mpr; intro γ
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ((Subgroup.ext_iff.mp h_gen.symm γ).mp (mem_top γ))
    rw [←AlgEquiv.smul_def, ←mem_stabilizerSubmonoid_iff]
    have : g b = b := by rw [map_sub, map_pow, hgz, sub_pow_char]; simp [b]
    exact mem_fixedBy_zpowers_iff_mem_fixedBy.mpr (mem_fixedBy.mpr this) n
  have h_int := IsIntegral.isIntegral z (R := F)
  have h := degree_dvd h_int; rw [hrank] at h
  have ⟨h_deg, h_mon⟩ := artinSchreierPoly_isMonicOfDegree a (Prime.one_lt hp)
  have h := (Prime.dvd_iff_eq hp (natDegree_eq_one_iff.mp.mt hz3)).mp h; rw [←h_deg] at h
  exact ⟨a, z, (eq_of_monic_of_dvd_of_natDegree_le (monic h_int) h_mon
    (dvd_iff.mpr (by aesop)) h.le).symm⟩

lemma cyclic_char_p_as_artin_schreier (F K : Type) [Field F] [Field K] [Algebra F K]
    [IsGalois F K] {p : ℕ} [CharP F p] (hp : Nat.Prime p) (hrank : Module.finrank F K = p) :
    ∃ a : F, IsSplittingField F K (X ^ p - X - C a) := by
  open IntermediateField Nat in
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  have ⟨a, z, hz⟩ := cyclic_char_p_as_param F K hp hrank
  let pol := X ^ p - X - C a; let iota := algebraMap F K; let pol' := map iota pol
  have hmap : pol' = X ^ p - X - C (iota a) := by aesop
  have ⟨h_deg, h_mon⟩ := artinSchreierPoly_isMonicOfDegree a (Prime.one_lt hp)
  have h_eval := minpoly.aeval F z; rw [hz] at h_eval
  have hroot1 : pol'.IsRoot ≠ ⊥ := Function.ne_iff.mpr ⟨z, (by aesop)⟩
  have : pol' ≠ 0 := map_monic_ne_zero h_mon
  have hroot2 := (roots_eq_zero_iff_isRoot_eq_bot this).mp.mt hroot1
  have splits : pol'.Splits := by
    rw [hmap] at *; exact artinSchreierPoly_isRoot_splits K (iota a) hp hroot2
  have adjoin : IntermediateField.adjoin F (pol.rootSet K) = ⊤ := by
    have hp0 := Prime.pos hp; rw [←hz] at h_deg; rw [←hrank] at hp0 h_deg
    have : z ∈ pol.rootSet K := (Monic.mem_rootSet h_mon).mpr h_eval
    have := adjoin_simple_le_iff.mpr (mem_adjoin_of_mem F this)
    have := FiniteDimensional.of_finrank_pos hp0
    have hd := (degree_eq_iff_natDegree_eq_of_pos hp0).mpr h_deg
    have := (Field.primitive_element_iff_minpoly_degree_eq F z).mpr hd; simp_all
  exact ⟨a, isSplittingField_iff_intermediateField.mpr ⟨splits, adjoin⟩⟩
