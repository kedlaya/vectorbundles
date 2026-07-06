module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

open IntermediateField Polynomial

lemma exists_root_of_natDegree_eq_one {R : Type u} [Field R] {p : R[X]} (h : p.natDegree = 1) :
   ∃ (x : R), p.IsRoot x :=
  exists_root_of_degree_eq_one ((degree_eq_iff_natDegree_eq_of_pos Nat.one_pos).mpr h)

@[simp]
lemma artinSchreierPoly_isMonicOfDegree {F : Type} [Field F] {p : ℕ} (a : F) (hp : 1 < p) :
    (X ^ p - X - C a).IsMonicOfDegree p := by
  rw [←natDegree_X_add_C a] at hp; rw [←sub_add_eq_sub_sub]
  exact IsMonicOfDegree.sub (isMonicOfDegree_X_pow F p) hp

@[simp]
lemma artinSchreierPoly_aeval {F : Type} {K : Type} {p : ℕ} [Field F] [Field K] [Algebra F K]
    (c : F) (z : K) : aeval z (X ^ p - X - C c) = z ^ p - z - (algebraMap F K) c := by
  simp only [aeval_sub, map_pow, aeval_X, aeval_C]

@[simp]
lemma artinSchreierPoly_taylor (F : Type) [Field F] {p : ℕ} [CharP F p] (a c : F)
    (hp : Nat.Prime p) : (X ^ p - X - C a).taylor c = X^p - X + C (c^p - c - a) := by
  have := fact_iff.mpr hp; calc (X ^ p - X - C a).taylor c
  _ = (X + C c)^p - (X + C c) - C a := by simp
  _ = X^p - X + C (c^p - c - a) := by grind [add_pow_char]

lemma artinSchreierPoly_isRoot_splits (F : Type) [Field F] {p : ℕ} [CharP F p] (a : F)
    (hp : Nat.Prime p) (hr : (X ^ p - X - C a).roots ≠ 0) : Splits (X ^ p - X - C a) := by
  have := fact_iff.mpr hp; have ⟨c, _⟩ := Multiset.exists_mem_of_ne_zero hr
  have := Splits.map (Subfield.splits_bot F p) (algebraMap _ F)
  have : ((X ^ p - X - C a).taylor c).Splits := by simp_all
  exact (splits_iff_comp_splits_of_natDegree_eq_one (natDegree_X_add_C c)).mpr this

lemma artinSchreierPoly_irred (F : Type) [Field F] {p : ℕ} [CharP F p] (a : F)
    (hp : Nat.Prime p) (hr : (X ^ p - X - C a).roots = 0) : Irreducible (X ^ p - X - C a) := by
  open AdjoinRoot Irreducible Multiset Nat UniqueFactorizationMonoid in
  have hp0 := Prime.pos hp; let pol := (X ^ p - X - C a); let S := factors pol
  have hmon := artinSchreierPoly_isMonicOfDegree a (Prime.one_lt hp)
  have hirr := fun b (a : b ∈ S) ↦ irreducible_of_factor b a
  have hirr2 := fun b (a : b ∈ S) ↦ dvd_of_mem_factors a
  have hirr3 := fun b (a : b ∈ S) ↦ ne_zero_of_natDegree_gt (natDegree_pos (hirr b a))
  have h0 := IsMonicOfDegree.ne_zero hmon; have hp0' := hp0; rw [←hmon.1] at hp0'
  have ⟨b, hb⟩ := exists_mem_factors h0 (not_isUnit_of_natDegree_pos pol hp0')
  have hbc : ∀ c, c ∈ S → b.natDegree ∣ c.natDegree := by
    intro c hc; have := fact_iff.mpr (irreducible_mul_leadingCoeff_inv.mpr (hirr c hc))
    let K := AdjoinRoot (c * C c.leadingCoeff⁻¹); have := (Algebra.charP_iff F K p).mp ‹CharP F p›
    have hm1 := AdjoinRoot.isAdjoinRootMonic _ (monic_mul_leadingCoeff_inv (hirr3 c hc))
    let i := algebraMap F K; have hroot1 := IsRoot.dvd (isRoot_root _) (map_dvd i (y := pol) ?_)
    let pol' := pol.map i; have hdiv := map_dvd i (hirr2 b hb)
    have hm0 := map_ne_zero (f := i) h0; have hmap : pol' = X^p - X - C (i a) := ?_
    have h : pol'.roots ≠ 0 := eq_zero_iff_forall_notMem.mp.mt ?_; subst pol'
    rw [hmap] at hm0 hdiv h; have hsp1 := artinSchreierPoly_isRoot_splits K _ hp h
    have hd := Irreducible.natDegree_dvd_finrank (hirr b hb) (Splits.of_dvd hsp1 hm0 hdiv)
    rw [IsAdjoinRootMonic.finrank hm1, natDegree_mul_leadingCoeff_self_inv c] at hd; repeat aesop
  have hn := fun f n (h: 0 < n) ↦ degree_eq_iff_natDegree_eq_of_pos h (R := F) (p := f); have := by
    have htd : ∀ t, t ∈ S.map natDegree → b.natDegree ∣ t := by aesop
    have hd := degree_eq_degree_of_associated (factors_prod h0); rw [(hn _ _ hp0).mpr hmon.1] at hd
    have hv := dvd_sum htd; rw [←natDegree_multiset_prod S (by aesop), (hn _ _ hp0).mp hd] at hv
    exact Prime.eq_one_or_self_of_dvd hp b.natDegree hv
  rcases this with h | h1
  · have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h
    have := (mem_roots h0).mpr (IsRoot.dvd hx (hirr2 b hb)); aesop
  · have h := associated_of_dvd_of_natDegree_le (hirr2 b hb) h0; rw [hmon.1, h1] at h
    exact Associated.irreducible (h (le_refl p)) (hirr b hb)

lemma artinSchreierPoly_irred_or_splits (F : Type) [Field F] {p : ℕ} [CharP F p] (a : F)
  (hp : Nat.Prime p) : Irreducible (X ^ p - X - C a) ∨ Splits (X ^ p - X - C a) := by
  by_cases hr : (X ^ p - X - C a).roots = 0
  · left; exact artinSchreierPoly_irred F a hp hr
  · right; exact artinSchreierPoly_isRoot_splits F a hp hr

lemma cyclic_char_p_as_param (F K : Type) [Field F] [Field K] [Algebra F K]
    [IsGalois F K] {p : ℕ} [CharP F p] (hp: Nat.Prime p) (hrank: Module.finrank F K = p) :
    ∃ a : F, ∃ z : K, minpoly F z = X ^ p - X - C a := by
  open Algebra FiniteDimensional Finset IsGalois MulAction Subgroup Nat minpoly in
  have := of_finrank_pos (hrank.trans_gt (Prime.pos hp)); have h_ord := card_aut_eq_finrank F K
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›; rw [hrank] at h_ord; have := fact_iff.mpr hp
  have ⟨g, h_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card h_ord)
  have h_ordg := orderOf_eq_card_of_zpowers_eq_top h_gen; rw [h_ord] at h_ordg; let rp := range p
  have ⟨y, hy⟩ := trace_surjective F K 1; let z := ∑ i : rp, (g^(i:ℕ)) y * i; let b := z^p - z
  have hz1 : ∑ i : rp, (g^(i+1:ℕ)) y * (i+1) = z := by
    let f := fun (i : ℕ) ↦ (g^i) y * i; let f1 := fun i ↦ f (i+1)
    have hp1 : p-1+1 = p := succ_pred_prime hp; calc _ = ∑ i : rp, f (i+1) := by simp [f]
    _ = ∑ i ∈ rp, f1 i := (sum_subtype rp (fun _ ↦ Iff.of_eq rfl) f1).symm
    _ = ∑ i ∈ rp, f i := by subst rp f1 f; rw [←hp1, sum_range_succ, sum_range_succ']; simp [hp1]
    _ = z := sum_subtype rp (fun _ ↦ Iff.of_eq rfl) f
  have hz2 : ∑ i : rp, (g^(i+1:ℕ)) y = ∑ σ : Gal(K/F), σ y := by open IsOfFinOrder in
    let f := fun (i : rp) ↦ g ^ (i+1:ℕ); refine sum_bijective f ?_ (by simp) (fun _ _ ↦ rfl)
    refine (Nat.bijective_iff_surjective_and_card f).mpr ⟨?_, ?_⟩
    · have := Classical.typeDecidableEq Gal(K/F)
      intro b; have h := mem_top (g ^ (-1:ℤ) * b); rw [←h_gen] at h
      have h := (mem_zpowers_iff_mem_range_orderOf (isOfFinOrder_of_finite g)).mp h
      rw [h_ordg, mem_image] at h; have ⟨i, hb1, hb2⟩ := h; use ⟨i, hb1⟩; subst f
      simp only [pow_succ' g, hb2, zpow_neg, zpow_one, mul_inv_cancel_left]
    · rw [h_ord, card_eq_finsetCard rp, card_range p]
  have h_int := IsIntegral.isIntegral z (R := F); have hgz : g z = z - 1 := calc
    _ = ∑ i : rp, g ((g^(i:ℕ)) y * i) := map_finset_sum _ _
    _ = ∑ i : rp, (g^(i+1:ℕ)) y * i := by simp [pow_succ' g]
    _ = ∑ i : rp, ((g^(i+1:ℕ)) y * (i+1) - (g^(i+1:ℕ)) y) := ?_
    _ = _ := by rw [sum_sub_distrib, hz1, hz2, ←trace_eq_sum_automorphisms, hy, map_one]
  have h := degree_dvd h_int; rw [hrank] at h; have ⟨a, _⟩ : b ∈ (⊥ : IntermediateField F K) := by
    apply (mem_bot_iff_fixed b).mpr; intro γ; rw [←AlgEquiv.smul_def, ←mem_stabilizerSubmonoid_iff]
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ((Subgroup.ext_iff.mp h_gen.symm γ).mp (mem_top _))
    apply fixedBy_subset_fixedBy_zpow; simp [b, hgz, sub_pow_char]
  have ⟨h_deg, h_mon⟩ := artinSchreierPoly_isMonicOfDegree a (Prime.one_lt hp)
  have hz3 := (mem_range_algebraMap_iff_fixed z (F := F)).mp.mt ?_
  have h := (Prime.dvd_iff_eq hp (natDegree_eq_one_iff.mp.mt hz3)).mp h; rw [←h_deg] at h
  exact ⟨a, z, (eq_of_monic_of_dvd_of_natDegree_le (monic h_int) h_mon
    (dvd_iff.mpr (by aesop)) h.le).symm⟩; repeat grind only

/- A Galois field extension of degree p between fields of characteristic p is the splitting field
   of a polynomial of the form X^p - X - a. -/
lemma cyclic_char_p_as_artin_schreier (F K : Type) [Field F] [Field K] [Algebra F K]
    [IsGalois F K] {p : ℕ} [CharP F p] (hp : Nat.Prime p) (hrank : Module.finrank F K = p) :
    ∃ a : F, IsSplittingField F K (X ^ p - X - C a) := by open Function Nat in
  have ⟨a, z, hz⟩ := cyclic_char_p_as_param F K hp hrank; let pol := X ^ p - X - C a
  let iota := algebraMap F K; have h_eval := minpoly.aeval F z; let pol' := map iota pol
  have ⟨h_deg, h_mon⟩ := artinSchreierPoly_isMonicOfDegree a (Prime.one_lt hp); rw [hz] at h_eval
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›; have splits : pol'.Splits := by
    have h : pol' ≠ 0 := map_monic_ne_zero h_mon
    have hr := (roots_eq_zero_iff_isRoot_eq_bot h).mp.mt (ne_iff.mpr ⟨z, ?_⟩)
    have hi : pol' = X ^ p - X - C (iota a) := ?_; rw [hi] at hr ⊢
    exact artinSchreierPoly_isRoot_splits K (iota a) hp hr; repeat aesop
  have adjoin : IntermediateField.adjoin F (pol.rootSet K) = ⊤ := by
    have hp0 := Prime.pos hp; rw [←hz] at h_deg; rw [←hrank] at hp0 h_deg
    have := adjoin_simple_le_iff.mpr (mem_adjoin_of_mem F ((Monic.mem_rootSet h_mon).mpr h_eval))
    have := FiniteDimensional.of_finrank_pos hp0
    have hd := (degree_eq_iff_natDegree_eq_of_pos hp0).mpr h_deg
    have := (Field.primitive_element_iff_minpoly_degree_eq F z).mpr hd; simp_all [pol]
  exact ⟨a, isSplittingField_iff_intermediateField.mpr ⟨splits, adjoin⟩⟩

/- For any field F of characteristic p, if an element x of an extension field of F has minimal
   polynomial X^P - X - C a for some a in F, then the polynomial X^p - X - C (a * x^(p-1)) has
   no root in F(x). -/
lemma artin_schreier_tower (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] {p : ℕ}
  [CharP F p] (hp : Nat.Prime p) (a : F) (x : K) (hx : minpoly F x = X^p - X - C a) :
    ¬∃ y : F⟮x⟯, y^p = y + (algebraMap F K) a * x ^ (p-1) := by open Algebra minpoly PowerBasis in
  by_contra; obtain ⟨y, hy⟩ := this
  have hp0 := Nat.Prime.pos hp; have hp1 := Nat.Prime.one_lt hp; have := fact_iff.mpr hp
  have h_d := (artinSchreierPoly_isMonicOfDegree a hp1).1; rw [←hx] at h_d
  let a' := (algebraMap F K) a; let t := a' * x^(p-1); have hx : x ^ p = x + a' := by
    have h := aeval F x; simp [hx] at h; rw [←sub_eq_zero, ←sub_sub, h]
  rw [←h_d] at hp1; have h_int := ne_zero_iff.mp (ne_zero_of_natDegree_gt hp1)
  rw [←sub_eq_zero] at hy; obtain ⟨f, h_pb, rfl⟩ := exists_eq_aeval (adjoin.powerBasis h_int) y
  rw [←aeval_coe, ←map_pow, ←map_frobenius_expand, map_expand, expand_aeval] at hy
  dsimp at hy h_pb; rw [h_d] at h_pb; let c := f.coeff (p-1); have : c^p = c + a := by
    let fr := frobenius F p; have hd := natDegree_map fr (p := f); let m := f.map fr; subst a'
    have h : m.taylor a - (f + monomial (p-1) a) = 0 := by
      refine eq_zero_of_dvd_of_natDegree_lt (dvd_iff (x := x).mpr ?_) ?_
      simp [taylor_apply, aeval_comp, ←hx]; exact hy; /- -/ compute_degree!; rw [hd]; simp_all
    have h1 : (m.taylor a).coeff (p-1) = c^p := by
      have h2 := (natDegree_taylor m a).trans hd; by_cases h0 : f.natDegree = p-1
      · rw [←h0, ←h2, ←leadingCoeff, leadingCoeff_taylor, leadingCoeff_map, leadingCoeff, h0]; rfl
      · subst c; (repeat rw [coeff_eq_zero_of_natDegree_lt]); rw [zero_pow]; repeat grind only
    rw [sub_eq_zero] at h; rw [←h1, h, coeff_add, coeff_monomial_same]
  have := Irreducible.not_isRoot_of_natDegree_ne_one (irreducible h_int) hp1.ne' (x := c); simp_all
