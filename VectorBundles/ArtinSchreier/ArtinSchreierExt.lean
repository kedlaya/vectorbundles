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
  exact (isMonicOfDegree_X_pow F p).sub hp

@[simp]
lemma artinSchreierPoly_aeval {F : Type} {K : Type} {p : ℕ} [Field F] [Field K] [Algebra F K]
    (c : F) (z : K) : aeval z (X ^ p - X - C c) = z ^ p - z - (algebraMap F K) c := by
  simp only [aeval_sub, map_pow, aeval_X, aeval_C]

@[simp]
lemma artinSchreierPoly_taylor (F : Type) [Field F] {p : ℕ} [CharP F p] (a c : F)
    (hp : p.Prime) : (X ^ p - X - C a).taylor c = X^p - X + C (c^p - c - a) := by
  have := fact_iff.mpr hp; calc (X ^ p - X - C a).taylor c
  _ = (X + C c)^p - (X + C c) - C a := by simp
  _ = X^p - X + C (c^p - c - a) := by grind [add_pow_char]

lemma artinSchreierPoly_isRoot_splits (F : Type) [Field F] {p : ℕ} [CharP F p] (a : F)
    (hp : p.Prime) (hr : (X ^ p - X - C a).roots ≠ 0) : Splits (X ^ p - X - C a) := by
  have := fact_iff.mpr hp; have ⟨c, _⟩ := Multiset.exists_mem_of_ne_zero hr
  have := (Subfield.splits_bot F p).map (algebraMap _ F)
  have : ((X ^ p - X - C a).taylor c).Splits := by simp_all
  exact (splits_iff_comp_splits_of_natDegree_eq_one (natDegree_X_add_C c)).mpr this

/- If every irreducible factor of a polynomial f has natDegree divisible by n,
   then so does f itself. -/
lemma dvd_natDegree_from_irred (F : Type) [Field F] {n : ℕ} (f : F[X])
  (h : ∀ d, Irreducible d → d ∣ f → n ∣ d.natDegree) : n ∣ f.natDegree := by
  by_cases h0 : f = 0; simp_all; /- -/  open Multiset PrincipalIdealRing in
  have ⟨hi, hS⟩ := factors_spec _ h0; have h1 := prod_eq_zero.mt (hS.symm.ne_zero_iff.mp h0)
  rw [←natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hS)]
  rw [natDegree_multiset_prod _ h1]; apply dvd_sum; simp only [mem_map]
  rintro - ⟨d, he, rfl⟩; exact (h d (hi d he) (hS.dvd_iff_dvd_right.mp (dvd_prod he)))

lemma artinSchreierPoly_irred (F : Type) [Field F] {p : ℕ} [Hp: CharP F p] (a : F)
    (hp : p.Prime) (hr : (X ^ p - X - C a).roots = 0) : Irreducible (X ^ p - X - C a) := by
  have hp0 := hp.pos; have hp0' := hp0; let pol := (X ^ p - X - C a); open AdjoinRoot Multiset in
  have hmon := artinSchreierPoly_isMonicOfDegree a hp.one_lt
  have h0 := IsMonicOfDegree.ne_zero hmon; rw [←hmon.1] at hp0'
  have ⟨b, hb1, hb2, hb3⟩ := exists_monic_irreducible_factor _ (not_isUnit_of_natDegree_pos _ hp0')
  have hbc : ∀ c, Irreducible c → c ∣ pol → b.natDegree ∣ c.natDegree := by
    intro c hc hc1; have := fact_iff.mpr (irreducible_mul_leadingCoeff_inv.mpr hc)
    have hc2 := hc.ne_zero; let K := AdjoinRoot (c * C c.leadingCoeff⁻¹); let i := algebraMap F K
    have hm1 := AdjoinRoot.isAdjoinRootMonic _ (monic_mul_leadingCoeff_inv hc2)
    rw [←c.natDegree_mul_leadingCoeff_self_inv, ←hm1.finrank]; let pol' := pol.map i
    have := (Algebra.charP_iff F K p).mp Hp; have hm0 := map_ne_zero (f := i) h0
    have hroot1 := (isRoot_root _).dvd (map_dvd i (y := pol) ?_); have hdiv := map_dvd i hb3
    have h : pol'.roots ≠ 0 := eq_zero_iff_forall_notMem.mp.mt ?_
    have hmap : pol' = X^p - X - C (i a) := ?_; subst pol'; rw [hmap] at hm0 hdiv h
    exact hb2.natDegree_dvd_finrank ((artinSchreierPoly_isRoot_splits _ _ hp h).of_dvd hm0 hdiv)
    repeat aesop
  have h := dvd_natDegree_from_irred F pol hbc; rw [hmon.1] at h
  rcases (Nat.dvd_prime hp).mp h with h | h1
  · have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h
    have := (mem_roots h0).mpr (hx.dvd hb3); aesop
  · exact ((associated_of_dvd_of_natDegree_le hb3 h0) (hmon.1.trans h1.symm).le).irreducible hb2

lemma artinSchreierPoly_irred_or_splits (F : Type) [Field F] {p : ℕ} [CharP F p] (a : F)
  (hp : p.Prime) : Irreducible (X ^ p - X - C a) ∨ Splits (X ^ p - X - C a) := by
  by_cases hr : (X ^ p - X - C a).roots = 0
  · left; exact artinSchreierPoly_irred F a hp hr
  · right; exact artinSchreierPoly_isRoot_splits F a hp hr

lemma cyclic_char_p_as_param (F K : Type) [Field F] [Field K] [Algebra F K]
    [IsGalois F K] {p : ℕ} [CharP F p] (hp : p.Prime) (hrank : Module.finrank F K = p) :
    ∃ a : F, ∃ z : K, minpoly F z = X ^ p - X - C a := by
  open Algebra FiniteDimensional Finset IsGalois MulAction Subgroup Nat minpoly in
  have := of_finrank_pos (hrank.trans_gt hp.pos); have h_ord := card_aut_eq_finrank F K
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
      have h := (isOfFinOrder_of_finite g).mem_zpowers_iff_mem_range_orderOf.mp h
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
  have ⟨h_deg, h_mon⟩ := artinSchreierPoly_isMonicOfDegree a hp.one_lt
  have hz3 := (mem_range_algebraMap_iff_fixed z (F := F)).mp.mt ?_
  have h := (hp.dvd_iff_eq (natDegree_eq_one_iff.mp.mt hz3)).mp h; rw [←h_deg] at h
  exact ⟨a, z, (eq_of_monic_of_dvd_of_natDegree_le (monic h_int) h_mon (dvd _ _ (by aesop))
    h.le).symm⟩; repeat grind only

/- A Galois field extension of degree p between fields of characteristic p is the splitting field
   of a polynomial of the form X^p - X - a. -/
lemma cyclic_char_p_as_artin_schreier (F K : Type) [Field F] [Field K] [Algebra F K]
    [IsGalois F K] {p : ℕ} [Hp: CharP F p] (hp : p.Prime) (hrank : Module.finrank F K = p) :
    ∃ a : F, IsSplittingField F K (X ^ p - X - C a) := by open Function in
  have ⟨a, z, hz⟩ := cyclic_char_p_as_param F K hp hrank; let pol := X ^ p - X - C a
  let iota := algebraMap F K; have h_eval := minpoly.aeval F z; let pol' := pol.map iota
  have ⟨h_deg, h_mon⟩ := artinSchreierPoly_isMonicOfDegree a hp.one_lt; rw [hz] at h_eval
  have := (Algebra.charP_iff F K p).mp Hp; have splits : pol'.Splits := by
    have h : pol' ≠ 0 := map_monic_ne_zero h_mon
    have hr := (roots_eq_zero_iff_isRoot_eq_bot h).mp.mt (ne_iff.mpr ⟨z, ?_⟩)
    have hi : pol' = X ^ p - X - C (iota a) := ?_; rw [hi] at hr ⊢
    exact artinSchreierPoly_isRoot_splits K _ hp hr; repeat aesop
  have adjoin : adjoin F (pol.rootSet K) = ⊤ := by
    have hp0 := hp.pos; rw [←hz] at h_deg; rw [←hrank] at hp0 h_deg
    have := adjoin_simple_le_iff.mpr (mem_adjoin_of_mem F (h_mon.mem_rootSet.mpr h_eval))
    have := FiniteDimensional.of_finrank_pos hp0
    have hd := (degree_eq_iff_natDegree_eq_of_pos hp0).mpr h_deg
    have := (Field.primitive_element_iff_minpoly_degree_eq F z).mpr hd; simp_all [pol]
  exact ⟨a, isSplittingField_iff_intermediateField.mpr ⟨splits, adjoin⟩⟩

/- For any field F of characteristic p, if an element x of an extension field of F has minimal
   polynomial X^p - X - C a for some a in F, then the polynomial X^p - X - C (a * x^(p-1)) has
   no root in F(x). -/
lemma artin_schreier_tower (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
  [CharP F p] (hp : p.Prime) (a : F) (x : K) (hx : minpoly F x = X^p - X - C a) :
    ¬∃ y : F⟮x⟯, y^p - y - (algebraMap F K) a * x ^ (p-1) = 0 := by open minpoly in
  by_contra; obtain ⟨y, hy⟩ := this; have hp1 := hp.one_lt; have := fact_iff.mpr hp
  have h_d := (artinSchreierPoly_isMonicOfDegree a hp1).1; rw [←hx] at h_d
  let a' := (algebraMap F K) a; let t := a' * x^(p-1); have hx : x ^ p = x + a' := by
    have h := aeval F x; simp [hx] at h; rw [←sub_eq_zero, ←sub_sub, h]
  rw [←h_d] at hp1; have h_int := ne_zero_iff.mp (ne_zero_of_natDegree_gt hp1)
  rw [←sub_eq_zero] at hy; obtain ⟨f, h_pb, rfl⟩ := (adjoin.powerBasis h_int).exists_eq_aeval y
  rw [←aeval_coe, ←map_pow, ←map_frobenius_expand, map_expand, expand_aeval] at hy
  dsimp at hy h_pb; rw [h_d] at h_pb; let c := f.coeff (p-1); have : c^p = c + a := by
    let fr := frobenius F p; have hd := natDegree_map fr (p := f); let m := f.map fr; subst a'
    have h : m.taylor a - (f + monomial (p-1) a) = 0 := by
      refine eq_zero_of_dvd_of_natDegree_lt (dvd _ x ?_) ?_
      simp [taylor_apply, aeval_comp, ←hx]; grind; compute_degree!; rw [hd]; simp_all [hp.pos]
    have h1 : (m.taylor a).coeff (p-1) = c^p := by
      have h2 := (natDegree_taylor m a).trans hd; by_cases h0 : f.natDegree = p-1
      · rw [←h0, ←h2, ←leadingCoeff, leadingCoeff_taylor, leadingCoeff_map, leadingCoeff, h0]; rfl
      · subst c; (repeat rw [coeff_eq_zero_of_natDegree_lt]); rw [zero_pow]; repeat grind only
    rw [sub_eq_zero] at h; rw [←h1, h, coeff_add, coeff_monomial_same]
  have := (irreducible h_int).not_isRoot_of_natDegree_ne_one hp1.ne' (x := c); simp_all
