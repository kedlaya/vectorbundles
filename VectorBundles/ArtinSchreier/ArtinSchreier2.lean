module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.MinpolyDiv

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.FieldTheory2
public import VectorBundles.ArtinSchreier.Polynomials
public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

open IntermediateField
open Polynomial

variable (F : Type) (K : Type) (p : ℕ) [Field F] [Field K]
  [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]

lemma finite_algebraic_closure_cyclic_prime (p : ℕ)
    (hp: Nat.Prime p) (h: Module.finrank F K = p)
      (hsep: IsGalois F K): ¬ ringChar F = p := by
  by_contra
  let iota := algebraMap F K
  have ha : ∃ (a : F), ∃ (x : K), minpoly F x = X ^ p -  X - C a :=
    cyclic_char_p_as_artin_schreier F K hp h hsep this
  obtain ⟨a, x, ha⟩ := ha
  have h_int : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  let aspol := X ^ p -  X -  C a
  have h_irras : Irreducible aspol ∧ aspol.Monic ∧ aspol.natDegree = p ∧ aspol.degree = p := by
    have h_minpoly : minpoly F x = aspol := by rw [ha]
    have h_natdeg : aspol.natDegree = p := by
      rw [← h_minpoly]
      rw [ha]
      simp
      refine FiniteField.X_pow_card_sub_X_natDegree_eq F ?_
      exact Nat.Prime.one_lt hp
    constructor
    · rw [← h_minpoly]
      exact minpoly.irreducible h_int
    constructor
    · rw [← h_minpoly]
      exact minpoly.monic h_int
    constructor
    · exact h_natdeg
    · refine (degree_eq_iff_natDegree_eq_of_pos ?_).mpr h_natdeg
      exact Nat.Prime.pos hp
  obtain ⟨h_irr, h_mon, h_natdeg, h_deg⟩ := h_irras

  let pb := IntermediateField.adjoin.powerBasis h_int
  have h_pbdim : pb.dim = p := by
    have h_pb_dim : (minpoly F (PowerBasis.gen pb)).natDegree = PowerBasis.dim pb := by
      apply PowerBasis.natDegree_minpoly
    calc
      pb.dim = (minpoly F (PowerBasis.gen pb)).natDegree := h_pb_dim.symm
      _ = (minpoly F x).natDegree := Nat.succ_inj.mp (congrArg Nat.succ h_pb_dim)
      _ = aspol.natDegree := natDegree_eq_of_degree_eq (congrArg degree ha)
      _ = p := h_natdeg

  let pol :=  X ^ p -  X -  C (x ^ (p-1) * (iota a))
  have hpol : pol.natDegree = p ∧ pol.Monic :=
    artin_schreier_poly (x ^ (p-1) * (iota a)) hp
  obtain ⟨hpol1, hpol2⟩ := hpol
  have hy : ∃ y : K, aeval y pol = 0 := by
    have h_poldeg : pol.degree = p := by
      refine (degree_eq_iff_natDegree_eq_of_pos ?_).mpr ?_
      exact Nat.Prime.pos hp
      exact Eq.symm ((fun {a b} ↦ Nat.succ_inj.mp) (congrArg Nat.succ (id (Eq.symm hpol1))))
    have _ : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    refine IsAlgClosed.exists_aeval_eq_zero K pol ?_
    rw [h_poldeg]
    refine Nat.cast_ne_zero.mpr ?_
    exact Nat.Prime.ne_zero hp
  obtain ⟨y, hy⟩ := hy
  have hy2 : y^p - y - x^(p-1) * iota a = 0 := by
    unfold aeval at hy
    unfold aevalEquiv at hy
    subst pol
    simp_all

  have h_sub : ∀ (z : K), z ∈ F⟮x⟯ := by
    intro z
    have h_minpolydeg : (minpoly F x).degree = ↑(Module.finrank F K) := by
      calc
        (minpoly F x).degree = (X ^ p - X - C a).degree := by rw [ha]
        _ = p := h_deg
        _ = ↑(Module.finrank F K) := Nat.cast_inj.mpr (id (Eq.symm h))
    have h_topcr : F⟮x⟯ = (⊤: IntermediateField F K) :=
      (Field.primitive_element_iff_minpoly_degree_eq F x).mpr h_minpolydeg
    have h_ext : ∀ (z : K), z ∈ F⟮x⟯ ↔ z ∈ (⊤: IntermediateField F K) :=
      IntermediateField.ext_iff.mp h_topcr
    exact (h_ext z).mpr mem_top

  have hy3 : ∃ (y0 : ↥F⟮x⟯), y0 = y := CanLift.prf y (h_sub y)
  obtain ⟨y0, hy3⟩ := hy3
  have hy4 : y0^p = y0 + x^(p-1) * iota a := by
    grind

  have h_pb_rep : ∀ (y : ↥F⟮x⟯), ∃ (f : Polynomial F), f.natDegree < PowerBasis.dim pb ∧
    y = (aeval (PowerBasis.gen pb)) f := PowerBasis.exists_eq_aeval pb
  obtain ⟨y0_rep, h_pb_rep_y01, h_pb_rep_y02⟩ := h_pb_rep y0
  have h_pb_rep_y01 : y0_rep.natDegree < p := by
    calc
      y0_rep.natDegree < pb.dim := h_pb_rep_y01
      _ = p := h_pbdim

  have _ : CharP F p := ringChar.of_eq this
  have _ : ExpChar F p := ExpChar.prime hp
  let frob := frobenius F p

  have h_rwx : x^p = x + (algebraMap F F⟮x⟯) a := by
    have h_evalx : aspol.aeval x = 0 := by
      calc
        aspol.aeval x = (minpoly F x).aeval x := AlgHom.congr_arg (aeval x) (id (Eq.symm ha))
        _ = 0 := minpoly.aeval F x
    subst aspol
    unfold aeval at h_evalx
    unfold aevalEquiv at h_evalx
    simp_all
    refine eq_add_of_sub_eq' ?_
    grind

  have h_power: (aeval pb.gen) ((map frob y0_rep).comp (X +  C a)) = y0 ^ p := by

    have h_pow_by_frobexp : ∀ (g: Polynomial F), (aeval pb.gen) (map frob ((expand F p) g)) =
      (aeval pb.gen g) ^ p  := by
        intro g
        calc
          (aeval pb.gen) (map frob ((expand F p) g)) = (aeval pb.gen) (g ^ p) := by
            refine AlgHom.congr_arg (aeval pb.gen) ?_
            exact map_frobenius_expand p g
          _ = (aeval pb.gen) g ^ p := map_pow (aeval pb.gen) g p

    have h_apply_frob_across_p : (map frob (y0_rep.comp (X ^ p))) = (map frob y0_rep).comp (X ^ p) := by
      calc
        (map frob (y0_rep.comp (X ^ p)))
        = (map frob y0_rep).comp (map frob (X ^ p)) := map_comp frob y0_rep (X ^ p)
        _ = (map frob y0_rep).comp (X ^ p) := by
          have h1 : map frob (X ^ p) = X ^ p := by
            calc
              map frob (X ^ p) = (map frob X)^p := Polynomial.map_pow frob p
              _ =  X ^ p := by
                have h2 : map frob X = X := map_X frob
                rw [h2]
          rw [h1]

    have h_eval_at_power :  ∀ (f : Polynomial F), (aeval (pb.gen^p)) f =
      (aeval pb.gen) (f.comp (X ^ p)) := by
      intro f
      calc
        aeval (pb.gen ^ p) f
        _ = aeval (aeval pb.gen (X ^ p)) f := by
            have h : aeval pb.gen ((X : Polynomial F) ^ p) = pb.gen ^ p :=
              aeval_X_pow pb.gen
            rw [h]
        _ = (aeval pb.gen) (f.comp (X ^ p)) := (aeval_comp pb.gen).symm

    have h_rwx_bp : pb.gen ^ p = pb.gen + (algebraMap F F⟮x⟯) a :=
      SetLike.coe_eq_coe.mp h_rwx

    have h_eval_at_sum : ∀ (f : Polynomial F), (aeval (pb.gen + (algebraMap F F⟮x⟯) a)) f =
      (aeval pb.gen) (f.comp (X  +  C a)) := by
      intro f
      calc
        aeval (pb.gen + (algebraMap F F⟮x⟯) a) f
        _ = aeval (aeval pb.gen (X  +  C a)) f := by
            have h : aeval pb.gen (X  +  C a) = pb.gen + (algebraMap F F⟮x⟯) a := by
              calc
                aeval pb.gen (X  +  C a)
                = aeval pb.gen ( X : Polynomial F) + aeval pb.gen (C a) := aeval_add pb.gen
                _ = pb.gen + aeval pb.gen (C a) := by rw [aeval_X pb.gen]
                _ = pb.gen + (algebraMap F F⟮x⟯) a := by rw [aeval_C pb.gen a]
            rw [h]
        _ = (aeval pb.gen) (f.comp (X  +  C a)) := (aeval_comp pb.gen).symm

    calc
      (aeval pb.gen) ((map frob y0_rep).comp (X +  C a))
      _ = (aeval (pb.gen + (algebraMap F F⟮x⟯) a)) (map frob y0_rep) := by
        rw [h_eval_at_sum (map frob y0_rep)]
      _ = (aeval (pb.gen^p)) (map frob y0_rep) := by
        rw [h_rwx_bp]
      _  = (aeval pb.gen) ((map frob y0_rep).comp (X ^ p)) := by
        rw [← h_eval_at_power (map frob y0_rep)]
      _  = (aeval pb.gen) ((expand F p) (map frob y0_rep)) := by rfl
      _  = (aeval pb.gen) (map frob ((expand F p) y0_rep)) := by
        rw [map_expand]
      _ = (aeval pb.gen y0_rep) ^ p := by
        rw [h_pow_by_frobexp y0_rep]
      _ = y0 ^ p := by
        rw [h_pb_rep_y02]

  let y0p_rep := (map frob y0_rep).comp (X + C a)
  let c := y0_rep.coeff (p-1)
  have h_y0rep : y0p_rep.natDegree < p ∧ y0p_rep.coeff (p-1) = c ^ p :=
    linear_substitution F p p a y0_rep hp (Nat.Prime.one_lt hp) h_pb_rep_y01
  obtain ⟨h_y0rep1, h_y0rep2⟩ := h_y0rep
  let y1p_rep := y0_rep + X ^ (p-1) *  C a
  have h_matchcoeff : y0p_rep.coeff (p-1) = y1p_rep.coeff (p-1) := by
    have h7 : ∀ f : Polynomial F, ((algebraMap F⟮x⟯ K) ∘ (aeval pb.gen)) f = aeval x f := by
      intro f
      have h1 : ↑((aeval pb.gen) (X : Polynomial F)) = aeval x (X : Polynomial F) := by
        unfold PowerBasis.gen
        unfold aeval
        unfold aevalEquiv
        simp_all
        refine exists_eq_subtype_mk_iff.mp ?_
        (expose_names; exact exists_apply_eq_apply (fun a => pb.1) (h_sub_1 x))
      aesop
    have h5 : aeval x y0p_rep = y0 ^p := by
      calc
        aeval x y0p_rep = aeval pb.gen y0p_rep := Eq.symm (h7 y0p_rep)
        _ = aeval pb.gen ((map frob y0_rep).comp (X + C a)) := by rfl
        _ = y0^p := by
          rw [h_power]
          simp
    have h4 : aeval x y1p_rep = y0 + x^(p-1) * iota a := by
      calc
        aeval x y1p_rep = aeval pb.gen y1p_rep := Eq.symm (h7 y1p_rep)
        _ = aeval pb.gen y0_rep + aeval pb.gen (X^(p-1) * (C a)) := by
          subst y1p_rep
          aesop
        _ = y0 + aeval pb.gen (X^(p-1) * (C a)) := by
          rw [h_pb_rep_y02]
        _ = y0 + pb.gen ^ (p-1) * iota a := by
          refine add_left_cancel_iff.mpr ?_
          unfold aeval
          unfold aevalEquiv
          have _ : (algebraMap F ↥F⟮x⟯) a * pb.gen ^ (p - 1) = pb.gen ^ (p - 1) * (algebraMap F ↥F⟮x⟯) a :=
            Algebra.commutes a (↑pb.gen ^ (p - 1))
          simp_all
          left
          rfl
        _ = y0 + x^(p-1) * iota a := by rfl
    have h6 : aeval x (y0p_rep - y1p_rep) = 0 := by
      calc
        aeval x (y0p_rep - y1p_rep) =  aeval x y0p_rep - aeval x y1p_rep :=
          aeval_sub x
        _ = 0 := by
          rw [h5, h4]
          exact sub_eq_zero.mpr hy4
    have h3 : (minpoly F x) ∣ (y0p_rep - y1p_rep) := by
      refine minpoly.dvd_iff.mpr ?_
      exact AddMonoidHom.mem_mker.mp h6
    have h1 : y0p_rep.natDegree < (minpoly F x).natDegree :=
      Nat.lt_of_lt_of_eq h_y0rep1 (id (Eq.symm h_pbdim))
    have h2 : y1p_rep.natDegree < (minpoly F x).natDegree :=
      calc
      y1p_rep.natDegree ≤ max y0_rep.natDegree (C a * X ^ (p - 1)).natDegree := by
        refine natDegree_add_le_of_le ?_ ?_
        exact Nat.le_refl y0_rep.natDegree
        have h7 : (C a * X ^ (p - 1)).natDegree = (X ^ (p - 1) * C a).natDegree := by
          refine (Monic.natDegree_mul_comm ?_ (C a)).symm
          exact monic_X_pow (p - 1)
        exact Nat.le_of_eq (id h7.symm)
      _ < p := by
        refine Nat.max_lt.mpr ?_
        constructor
        · (expose_names; exact Nat.lt_of_lt_of_eq h_pb_rep_y01_1 h_pbdim)
        · refine (Nat.le_sub_one_iff_lt ?_).mp ?_
          exact Nat.zero_lt_of_lt h_y0rep1
          apply Polynomial.natDegree_C_mul_X_pow_le a (p-1)
      _ = (minpoly F x).natDegree :=
        Nat.succ_inj.mp (congrArg Nat.succ (id h_pbdim.symm))
    have h : y0p_rep = y1p_rep :=
      congruence_low_degree h3 h1 h2 (minpoly.monic h_int)
    exact ext_iff.mp h (p-1)
  have h_fieldeq: c^p - c = a := by
    calc
      c^p - c = y0p_rep.coeff (p-1) - c := by
        refine sub_left_inj.mpr ?_
        exact Eq.symm h_y0rep2
      _ = y1p_rep.coeff (p-1) - c := sub_left_inj.mpr h_matchcoeff
      _ = y0_rep.coeff (p-1) + (X ^ (p-1) * C a).coeff (p-1) - c := by
        refine sub_left_inj.mpr ?_
        exact coeff_add y0_rep (X ^ (p-1) * C a) (p - 1)
      _ = y0_rep.coeff (p-1) + a - c := by
        refine sub_left_inj.mpr ?_
        refine (add_right_inj (y0_rep.coeff (p - 1))).mpr ?_
        have h_moncoeff : ((monomial (p-1)) a).coeff (p-1) = if (p-1) = (p-1) then a else 0 :=
          coeff_monomial
        unfold monomial at h_moncoeff
        simp
      _ = c + a - c := sub_right_inj.mpr rfl
      _ = a := by ring
  have h_deg1 : (minpoly F x).natDegree ≤ 1 := by
    have _ : Fact (Nat.Prime p) := fact_iff.mpr hp
    have _ : CharP K p := by
      (expose_names; exact (Algebra.charP_iff F K p).mp h_1)
    let x1 := x - iota c
    have hn : ∃ (n : ℤ), ↑n = x1 :=
      have fieldeq : x1^p = x1 := by
        calc
          x1^p = (x - iota c)^p := by rfl
          _ = x^p - iota c ^ p := sub_pow_char x (iota c)
          _ = x + iota a - iota c ^ p := sub_left_inj.mpr h_rwx
          _ = x + iota (c^p - c) - iota c ^ p := by
            rw [h_fieldeq]
          _ = x + iota (c^p) - iota c - iota c ^ p := by
            have hsub : iota (c^p - c) = iota (c^p) - iota c :=
              algebraMap.coe_sub (c ^ p) c
            rw [hsub]
            refine sub_left_inj.mpr ?_
            exact add_sub x (iota (c ^ p)) (iota c)
          _ = x + iota c ^ p - iota c - iota c ^ p := by simp
          _ = x1 := by ring
      have h_bot : x1 ∈ (⊥ : Subfield K) :=
        (Subfield.mem_bot_iff_pow_eq_self K p).mpr fieldeq
      (mem_bot_iff_intCast p K).mp h_bot
    obtain ⟨n, hn⟩ := hn
    have _ : ∃ d : F, x = iota d := by
      use (n + c)
      calc
      x = x1 + iota c := Eq.symm (sub_add_cancel x (iota c))
      _ = n + iota c := by rw [← hn]
      _ = iota n + iota c := by
        refine (add_left_inj (iota c)).mpr ?_
        exact Eq.symm (map_intCast iota n)
      _ = iota (n + c) := Eq.symm (algebraMap.coe_add (↑n) c)
    let pol1 :=  X - C (n + c)
    have _ : minpoly F x ∣ pol1 := by
      have h_evalpol1 : aeval x pol1 = 0 := by
        calc
        aeval x pol1 = aeval x ( X - C (n + c)) := by
          rfl
        _ =  aeval x (X : Polynomial F) - aeval x ( C (n + c)) :=
          aeval_sub x
        _ = x - aeval x ( C (n + c)) := by
          rw [aeval_X x]
        _ = x - iota (n + c) := by
          rw [aeval_C x (↑n + c)]
        _ = x1 + iota c - iota (n + c) := by
          rw [← sub_add_cancel x (iota c)]
        _ = 0 := by
          rw [← hn]
          simp
      exact minpoly.dvd_iff.mpr h_evalpol1
    calc
      (minpoly F x).natDegree ≤ pol1.natDegree := by
        (expose_names; refine natDegree_le_of_dvd h_6 ?_)
        exact X_sub_C_ne_zero (↑n + c)
      _ = 1 := natDegree_X_sub_C (n+c)
      _ ≤ 1 := by exact NeZero.one_le
  have _ : 1 < 1 := by
    calc
      1 < p := Nat.Prime.one_lt hp
      p = aspol.natDegree := h_natdeg.symm
      _ = (minpoly F x).natDegree := (natDegree_eq_of_degree_eq (congrArg degree ha)).symm
      _ ≤ 1 := h_deg1
  simp_all
