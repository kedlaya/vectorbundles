module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Finite.Basic
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
public import Mathlib.RingTheory.FreeRing
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField
open Polynomial

lemma linear_substitution (F : Type) [Field F] (p : ℕ) [ExpChar F p] (d : ℕ) (a : F) (y0_rep : Polynomial F)
  (hp: Nat.Prime p) (hd: d > 1) (hdeg: y0_rep.natDegree < d) :
  let y0p_rep := (Polynomial.comp (Polynomial.map (frobenius F p) y0_rep)) (Polynomial.X + Polynomial.C a);
  y0p_rep.natDegree < d ∧ y0p_rep.coeff (d-1) = (y0_rep.coeff (d-1)) ^ p := by

    have h_coeff:  (map (frobenius F p) y0_rep).coeff = (frobenius F p) ∘ y0_rep.coeff := by
      apply Polynomial.coeff_map_eq_comp y0_rep (frobenius F p)
    let y0_high := (monomial (d-1)) (y0_rep.coeff (d-1))
    let y0_low := y0_rep.erase (d-1)
    have h_sum: y0_high + y0_low = y0_rep :=
      Polynomial.monomial_add_erase y0_rep (d-1)
    have h_deg1 : y0_rep.natDegree ≤ d-1 :=
      Nat.le_sub_one_of_lt hdeg
    have h_deg2: ∀ (f : Polynomial F), ((Polynomial.comp (map (frobenius F p) f)) (Polynomial.X + Polynomial.C a)).natDegree ≤
      f.natDegree := by
        intro f
        calc
        ((Polynomial.comp (map (frobenius F p) f)) (Polynomial.X + Polynomial.C a)).natDegree ≤
          (map (frobenius F p) f).natDegree * (Polynomial.X + Polynomial.C a).natDegree :=
          Polynomial.natDegree_comp_le
        _ = (map (frobenius F p) f).natDegree * 1 :=
          Nat.succ_inj.mp
            (congrArg Nat.succ
              (congrArg (HMul.hMul (Polynomial.map (frobenius F p) f).natDegree) (natDegree_X_add_C a)))
        _ = (map (frobenius F p) f).natDegree := Nat.mul_one (Polynomial.map (frobenius F p) f).natDegree
        _ ≤ f.natDegree := Polynomial.natDegree_map_le

    let y0p_rep := (Polynomial.comp (Polynomial.map (frobenius F p) y0_rep)) (Polynomial.X + Polynomial.C a)
    constructor
    · calc
      y0p_rep.natDegree
        ≤ y0_rep.natDegree := h_deg2 y0_rep
      _ ≤ d-1 := h_deg1
      _ < d := Nat.sub_one_lt_of_lt hdeg

    have h_deg: y0_low.natDegree ≤ d-2 := by
      have _ : p ≥ 2 := Nat.Prime.two_le hp
      refine natDegree_le_iff_coeff_eq_zero.mpr ?_
      intro N hN
      by_cases N = d - 1
      · subst N
        exact Polynomial.erase_same y0_rep (d-1)
      · rename_i h
        calc
        y0_low.coeff N = y0_rep.coeff N := Polynomial.erase_ne y0_rep (d-1) N h
        _ = 0 := by
          refine coeff_eq_zero_of_natDegree_lt ?_
          calc
            y0_rep.natDegree ≤ d-1 := h_deg1
            _ < N := by
              grind
    let y0p_low := (Polynomial.comp (map (frobenius F p) y0_low)) (Polynomial.X + Polynomial.C a)
    let y0p_high := (Polynomial.comp (map (frobenius F p) y0_high)) (Polynomial.X + Polynomial.C a)
    have h_map: map (frobenius F p) y0_rep = map (frobenius F p) y0_low + map (frobenius F p) y0_high := by
      calc
      map (frobenius F p) y0_rep = map (frobenius F p) (y0_high + y0_low) := by
        rw [← h_sum]
      _ = map (frobenius F p) y0_high + map (frobenius F p) y0_low :=
        Polynomial.map_add (frobenius F p)
      _ = map (frobenius F p) y0_low + map (frobenius F p) y0_high :=
        AddCommMagma.add_comm (Polynomial.map (frobenius F p) y0_high)
          (Polynomial.map (frobenius F p) y0_low)
    have h_add : y0p_rep = y0p_low + y0p_high := by
      calc
      y0p_rep = (Polynomial.comp (map (frobenius F p) y0_rep)) (Polynomial.X + Polynomial.C a) := by rfl
      _ =  (Polynomial.comp (map (frobenius F p) y0_low + map (frobenius F p) y0_high)) (Polynomial.X + Polynomial.C a) := by
        exact Polynomial.ext (congrFun (congrArg coeff (congrFun (congrArg comp h_map) (X + C a))))
      _ = y0p_low + y0p_high := add_comp
    have h_deglow : y0p_low.natDegree ≤ d-2 := by calc
      y0p_low.natDegree
      ≤ y0_low.natDegree := h_deg2 y0_low
      _ ≤ d-2 := h_deg

    let c := y0_rep.coeff (d-1)
    have h_highcoeff : y0p_high.coeff (d-1) = c^p := by
      have h_highval : y0p_high =  (C (c^p)) * (Polynomial.X + Polynomial.C a) ^ (d-1) := by calc
        y0p_high = Polynomial.comp (map (frobenius F p) y0_high) (Polynomial.X + Polynomial.C a) := by rfl
        _ = Polynomial.comp (map (frobenius F p) (monomial (d-1) (y0_rep.coeff (d-1)))) (Polynomial.X + Polynomial.C a) := by rfl
        _ = Polynomial.comp (monomial (d-1) ((frobenius F p) c)) (Polynomial.X + Polynomial.C a) := by
          aesop
        _ = Polynomial.comp (monomial (d-1) (c^p)) (Polynomial.X + Polynomial.C a) := Polynomial.ext (congrFun rfl)
        _ = (C (c^p)) * (Polynomial.X + Polynomial.C a) ^ (d-1) := Polynomial.monomial_comp (d-1)
      have h_powcoeff: ((X + C a) ^ (d - 1)).coeff (d-1) = 1 := by calc
        ((X + C a) ^ (d - 1)).coeff (d-1) = a^(d-1-(d-1)) * ((d-1).choose (d-1) : F) := Polynomial.coeff_X_add_C_pow a (d-1) (d-1)
        _ = (1 : F) := by simp
      calc
      y0p_high.coeff (d-1)
        = ((Polynomial.comp (map (frobenius F p) y0_high)) (Polynomial.X + Polynomial.C a)).coeff (d-1) := by rfl
        _ = ( (C (c^p)) * (Polynomial.X + Polynomial.C a) ^ (d-1)).coeff (d-1) := by
          grind
        _ = c^p * ( (Polynomial.X + Polynomial.C a) ^ (d-1)).coeff (d-1) :=
          coeff_C_mul ((X + C a) ^ (d - 1))
        _ = c^p := by aesop
    calc
      y0p_rep.coeff (d-1) = (y0p_low + y0p_high).coeff (d-1) := by aesop
      _ = y0p_low.coeff (d-1) + y0p_high.coeff (d-1) := Polynomial.coeff_add y0p_low y0p_high (d-1)
      _ = 0 + y0p_high.coeff (d-1) := by
        refine add_right_cancel_iff.mpr ?_
        refine coeff_eq_zero_of_natDegree_lt ?_
        refine (Nat.le_pred_iff_lt ?_).mp h_deglow
        refine Nat.zero_lt_sub_of_lt ?_
        exact hd
      _ = y0p_high.coeff (d-1) := by simp
      _ = c^p := h_highcoeff

lemma finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (h: Module.finrank F K = p)
  (hsep: IsGalois F K): ¬ ringChar F = p := by

  by_contra
  have ha :  ∃ (a : F), ∃ (x : K),
    minpoly F x = Polynomial.X ^ p - Polynomial.X - Polynomial.C a := by
    apply cyclic_char_p_as_artin_schreier F K p hp h hsep this
  obtain ⟨a, x, ha⟩ := ha
  have h_int : IsIntegral F x :=
    Algebra.IsIntegral.isIntegral x
  let aspol :=  Polynomial.X ^ p - Polynomial.X - Polynomial.C a
  have h_irras : Irreducible aspol ∧ aspol.Monic ∧ aspol.natDegree = p ∧ aspol.degree = p := by
    have h_minpoly : minpoly F x = aspol := by
      exact Polynomial.ext (congrFun (congrArg Polynomial.coeff ha))
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
    refine (Polynomial.degree_eq_iff_natDegree_eq_of_pos ?_).mpr h_natdeg
    exact Nat.Prime.pos hp
  obtain ⟨h_irr, h_mon, h_natdeg, h_deg⟩ := h_irras

  let pb := IntermediateField.adjoin.powerBasis h_int
  have h_pbdim : pb.dim = p := by
    have h_pb_dim : (minpoly F (PowerBasis.gen pb)).natDegree = PowerBasis.dim pb := by
      apply PowerBasis.natDegree_minpoly
    calc
      pb.dim = (minpoly F (PowerBasis.gen pb)).natDegree := by
        symm
        exact h_pb_dim
      _ = (minpoly F x).natDegree := by
        exact Nat.succ_inj.mp (congrArg Nat.succ h_pb_dim)
      _ = aspol.natDegree := by exact
        Polynomial.natDegree_eq_of_degree_eq (congrArg Polynomial.degree ha)
      _ = p := h_natdeg

  let pol := Polynomial.X ^ p + (- Polynomial.X - Polynomial.C (x ^ (p-1) * ((algebraMap F K) a)))
  have hpol : pol.natDegree = p ∧ pol.Monic :=
    artin_schreier_poly p (x ^ (p-1) * ((algebraMap F K) a)) hp
  obtain ⟨hpol1, hpol2⟩ := hpol
  have _ : pol.degree = p := by
    refine (Polynomial.degree_eq_iff_natDegree_eq_of_pos ?_).mpr ?_
    exact Nat.Prime.pos hp
    exact Eq.symm ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (id (Eq.symm hpol1))))
  have hy : ∃ y : K, Polynomial.aeval y pol = 0 := by
    have _ : IsAlgClosed K := by
      exact IsAlgClosure.isAlgClosed F
    refine IsAlgClosed.exists_aeval_eq_zero K pol ?_
    simp_all
    exact Nat.Prime.ne_zero hp
  obtain ⟨y, hy ⟩ := hy
  have hy2 : y^p = y + x^(p-1) * (algebraMap F K) a := by
    unfold Polynomial.aeval at hy
    unfold Polynomial.aevalEquiv at hy
    subst pol
    simp_all
    grind

  have h_sub : ∀ (z : K), z ∈ F⟮x⟯ := by
    have h_topcr : F⟮x⟯ = (⊤: IntermediateField F K) ↔ (minpoly F x).degree = ↑(Module.finrank F K) := by
      apply Field.primitive_element_iff_minpoly_degree_eq
    obtain ⟨cr1, cr2⟩ := h_topcr
    have cr3 : (minpoly F x).degree = ↑(Module.finrank F K) := by
      calc
        (minpoly F x).degree = (X ^ p - X - C a).degree := by simp_all
        _ = aspol.degree := by rfl
        _ = p := h_deg
        _ = ↑(Module.finrank F K) := Nat.cast_inj.mpr (id (Eq.symm h))
    specialize cr2 cr3
    have h_ext : F⟮x⟯ = (⊤: IntermediateField F K) ↔ ∀ (z : K), z ∈ F⟮x⟯ ↔ z ∈ (⊤: IntermediateField F K) :=
      IntermediateField.ext_iff
    obtain ⟨h_ext1, h_ext2⟩ := h_ext
    specialize h_ext1 cr2
    intro z
    specialize h_ext1 z
    obtain ⟨h_ext3, h_ext4⟩ := h_ext1
    have h_mem_top : z ∈ (⊤: IntermediateField F K) := by
      exact mem_top
    specialize h_ext4 h_mem_top
    exact h_ext4

  have hy3 : ∃ (y0 : ↥F⟮x⟯), y0 = y := by
    specialize h_sub y
    exact CanLift.prf y h_sub
  obtain ⟨y0, hy3 ⟩ := hy3
  have hy4 : y0^p = y0 + x^(p-1) * (algebraMap F K) a := by
    simp_all

  have h_pb_rep : ∀ (y : ↥F⟮x⟯), ∃ (f : Polynomial F), f.natDegree < PowerBasis.dim pb ∧ y = (Polynomial.aeval (PowerBasis.gen pb)) f := by
    apply PowerBasis.exists_eq_aeval pb

  obtain ⟨y0_rep, h_pb_rep_y01, h_pb_rep_y02⟩ := h_pb_rep y0
  have h_pb_rep_y01 : y0_rep.natDegree < p := by
    calc
      y0_rep.natDegree < pb.dim := h_pb_rep_y01
      _ = p := h_pbdim

  have _ : CharP F p := by
    exact ringChar.of_eq this
  have _ : ExpChar F p := by
    exact ExpChar.prime hp

  have h_rwx : x^p = x + (algebraMap F F⟮x⟯) a := by
    have h_evalx : aspol.aeval x = 0 := by
      calc
        aspol.aeval x = (minpoly F x).aeval x := by
          exact AlgHom.congr_arg (Polynomial.aeval x) (id (Eq.symm ha))
        _ = 0 := minpoly.aeval F x
    subst aspol
    unfold Polynomial.aeval at h_evalx
    unfold Polynomial.aevalEquiv at h_evalx
    simp_all
    refine eq_add_of_sub_eq' ?_
    grind

  have h_power : (Polynomial.aeval pb.gen) ((Polynomial.comp (map (frobenius F p) y0_rep)) (Polynomial.X + Polynomial.C a))
        = y0 ^ p := by

    have h_pow_by_frobexp : ∀ (g: Polynomial F), (Polynomial.aeval pb.gen) (map (frobenius F p) ((Polynomial.expand F p) g)) =
      (aeval pb.gen g) ^ p  := by
        intro g
        calc
          (Polynomial.aeval pb.gen) (map (frobenius F p) ((Polynomial.expand F p) g)) = (Polynomial.aeval pb.gen) (g ^ p) := by
            refine AlgHom.congr_arg (aeval pb.gen) ?_
            exact map_frobenius_expand p g
          _ = (Polynomial.aeval pb.gen) g ^ p := map_pow (aeval pb.gen) g p

    have h_apply_frob_across_p : (map (frobenius F p) (y0_rep.comp (Polynomial.X ^ p)))
          = (map (frobenius F p) y0_rep).comp (Polynomial.X ^ p)  := by
          calc
            (map (frobenius F p) (y0_rep.comp (Polynomial.X ^ p)))
              = (map (frobenius F p) y0_rep).comp (map (frobenius F p) (Polynomial.X ^ p)) := by
                exact map_comp (frobenius F p) y0_rep (X ^ p)
            _ = (map (frobenius F p) y0_rep).comp (Polynomial.X ^ p) := by
              have _ : map (frobenius F p) (Polynomial.X ^ p) = Polynomial.X ^ p := by
                calc
                  map (frobenius F p) (Polynomial.X ^ p) = (map (frobenius F p) Polynomial.X)^p := by
                    exact Polynomial.map_pow (frobenius F p) p
                  _= Polynomial.X ^ p := by
                    have _ : map (frobenius F p) Polynomial.X = Polynomial.X := by
                      exact map_X (frobenius F p)
                    (expose_names; exact
                        Polynomial.ext (congrFun (congrArg coeff (congrFun (congrArg HPow.hPow h_4) p))))
              (expose_names;
                exact
                  Polynomial.ext
                    (congrFun
                      (congrArg coeff (congrArg (Polynomial.map (frobenius F p) y0_rep).comp h_4))))

    have h_eval_at_power :  ∀ (f : Polynomial F), (Polynomial.aeval (pb.gen^p)) f =
      (Polynomial.aeval pb.gen) (f.comp (Polynomial.X ^ p)) := by
      intro f
      have _ : aeval pb.gen (f.comp (Polynomial.X ^ p)) = aeval (aeval pb.gen (Polynomial.X ^ p)) f :=
        Polynomial.aeval_comp pb.gen
      calc
        aeval (pb.gen ^ p) f
        _ = aeval (aeval pb.gen (Polynomial.X ^ p)) f := by
            have _ : aeval pb.gen ((Polynomial.X : Polynomial F) ^ p) = pb.gen ^ p := by
              exact aeval_X_pow pb.gen
            (expose_names; exact AlgHom.congr_fun (congrArg aeval (id (Eq.symm h_5))) f)
        _ = (Polynomial.aeval pb.gen) (f.comp (Polynomial.X ^ p)) := by
          exact Eq.symm (aeval_comp pb.gen)

    have h_rwx_bp : pb.gen ^ p = pb.gen + (algebraMap F F⟮x⟯) a := by
      exact SetLike.coe_eq_coe.mp h_rwx

    have h_eval_at_sum : ∀ (f : Polynomial F), (Polynomial.aeval (pb.gen + (algebraMap F F⟮x⟯) a )) f =
      (Polynomial.aeval pb.gen) (f.comp (Polynomial.X  + Polynomial.C a)) := by
      intro f
      have _ : aeval pb.gen (f.comp (Polynomial.X  + Polynomial.C a)) = aeval (aeval pb.gen (Polynomial.X  + Polynomial.C a)) f :=
        Polynomial.aeval_comp pb.gen
      calc
        aeval (pb.gen + (algebraMap F F⟮x⟯) a) f
        _ = aeval (aeval pb.gen (Polynomial.X  + Polynomial.C a)) f := by
            have _ : aeval pb.gen (Polynomial.X  + Polynomial.C a) = pb.gen + (algebraMap F F⟮x⟯) a := by
              calc
                aeval pb.gen (Polynomial.X  + Polynomial.C a) = aeval pb.gen (Polynomial.X : Polynomial F)
                   + aeval pb.gen (Polynomial.C a) := aeval_add pb.gen
                _ = pb.gen + aeval pb.gen (Polynomial.C a) := by
                  refine (add_left_inj ((aeval pb.gen) (C a))).mpr ?_
                  exact aeval_X pb.gen
                _ = pb.gen + (algebraMap F F⟮x⟯) a := by
                  refine add_left_cancel_iff.mpr ?_
                  exact aeval_C pb.gen a
            (expose_names; exact AlgHom.congr_fun (congrArg aeval (id (Eq.symm h_5))) f)
        _ = (Polynomial.aeval pb.gen) (f.comp (Polynomial.X  + Polynomial.C a)) := by
          exact Eq.symm (aeval_comp pb.gen)


    calc
      (Polynomial.aeval pb.gen) ((Polynomial.comp (map (frobenius F p) y0_rep)) (Polynomial.X + Polynomial.C a))
      _ = (Polynomial.aeval (pb.gen + (algebraMap F F⟮x⟯) a)) (map (frobenius F p) y0_rep) := by
          exact
            SetLike.coe_eq_coe.mp
              (congrArg Subtype.val (h_eval_at_sum (Polynomial.map (frobenius F p) y0_rep))).symm
      _ = (Polynomial.aeval (pb.gen^p)) (map (frobenius F p) y0_rep) := by
          exact
            AlgHom.congr_fun (congrArg aeval (id (Eq.symm h_rwx_bp)))
              (Polynomial.map (frobenius F p) y0_rep)
      _  = (Polynomial.aeval pb.gen) ((Polynomial.comp (map (frobenius F p) y0_rep)) (Polynomial.X ^ p)) := by
          exact
            SetLike.coe_eq_coe.mp
              (congrArg Subtype.val (h_eval_at_power (Polynomial.map (frobenius F p) y0_rep)))
      _  = (Polynomial.aeval pb.gen) ((Polynomial.expand F p) (map (frobenius F p) y0_rep)) := by
          exact AlgHom.congr_arg (aeval pb.gen) rfl
      _  = (Polynomial.aeval pb.gen) (map (frobenius F p) ((Polynomial.expand F p) y0_rep)) := by
        refine Eq.symm (AlgHom.congr_arg (aeval pb.gen) ?_)
        exact map_expand
      _ = (aeval pb.gen y0_rep) ^ p := by
        exact SetLike.coe_eq_coe.mp (congrArg Subtype.val (h_pow_by_frobexp y0_rep))
      _ = y0 ^ p := by
        exact
          SetLike.coe_eq_coe.mp
            (congrArg Subtype.val (congrFun (congrArg HPow.hPow (id (Eq.symm h_pb_rep_y02))) p))

  let y0p_rep := (Polynomial.comp (map (frobenius F p) y0_rep)) (Polynomial.X + Polynomial.C a)
  let c := y0_rep.coeff (p-1)
  let y1p_rep := y0_rep + Polynomial.X ^ (p-1) * Polynomial.C a
  have h_y0rep : y0p_rep.natDegree < p ∧ y0p_rep.coeff (p-1) = c ^ p :=
    linear_substitution F p p a y0_rep hp (Nat.Prime.one_lt hp) h_pb_rep_y01
  obtain ⟨h_y0rep1, h_y0rep2⟩ := h_y0rep
  have h_matchcoeff : y0p_rep.coeff (p-1) = y1p_rep.coeff (p-1) := by
    have h7 : ∀ f : Polynomial F, ((algebraMap F⟮x⟯ K) ∘ (Polynomial.aeval pb.gen)) f = Polynomial.aeval x f := by
      intro f
      have h1 : ↑((Polynomial.aeval pb.gen) (X : Polynomial F)) = Polynomial.aeval x (X : Polynomial F) := by
        unfold PowerBasis.gen
        unfold aeval
        unfold aevalEquiv
        simp_all
        refine exists_eq_subtype_mk_iff.mp ?_
        (expose_names; exact exists_apply_eq_apply (fun a => pb.1) (h_sub_1 x))
      aesop
    have h5 : Polynomial.aeval x y0p_rep = y0 ^p := by
      calc
        Polynomial.aeval x y0p_rep = Polynomial.aeval pb.gen y0p_rep := Eq.symm (h7 y0p_rep)
        _ = Polynomial.aeval pb.gen ((Polynomial.map (frobenius F p) y0_rep).comp (X + C a)) := by rfl
        _ = y0^p := by
          convert h_power
          simp_all
    have h4 : Polynomial.aeval x y1p_rep = y0 + x^(p-1) * (algebraMap F K) a := by
      calc
        Polynomial.aeval x y1p_rep = Polynomial.aeval pb.gen y1p_rep := Eq.symm (h7 y1p_rep)
        _ = Polynomial.aeval pb.gen y0_rep + Polynomial.aeval pb.gen (X^(p-1) * (C a)) := by
          subst y1p_rep
          aesop
        _ = y0 + Polynomial.aeval pb.gen (X^(p-1) * (C a)) := by
          rw [h_pb_rep_y02]
        _ = y0 + pb.gen ^ (p-1) * (algebraMap F K) a := by
          refine add_left_cancel_iff.mpr ?_
          unfold aeval
          unfold aevalEquiv
          have _ : (algebraMap F ↥F⟮x⟯) a * pb.gen ^ (p - 1) = pb.gen ^ (p - 1) * (algebraMap F ↥F⟮x⟯) a := by
            (expose_names; exact Algebra.commutes a (↑pb.gen ^ (p - 1)))
          simp_all
        _ = y0 + x^(p-1) * (algebraMap F K) a := by
          exact (add_left_inj (↑pb.gen ^ (p - 1) * (algebraMap F K) a)).mpr rfl
    have h6 : Polynomial.aeval x (y0p_rep - y1p_rep) = 0 := by
      calc
        Polynomial.aeval x (y0p_rep - y1p_rep) =  Polynomial.aeval x y0p_rep - Polynomial.aeval x y1p_rep :=
          aeval_sub x
        _ = 0 := by
          rw [h5]
          rw [h4]
          exact sub_eq_zero.mpr hy4
    have h3 : (minpoly F x) ∣ (y0p_rep - y1p_rep) := by
      refine minpoly.dvd_iff.mpr ?_
      exact AddMonoidHom.mem_mker.mp h6
    have h1 : y0p_rep.natDegree < (minpoly F x).natDegree := by
      exact Nat.lt_of_lt_of_eq h_y0rep1 (id (Eq.symm h_pbdim))
    have h2 : y1p_rep.natDegree < (minpoly F x).natDegree :=
      calc
      y1p_rep.natDegree ≤ max y0_rep.natDegree (C a * X ^ (p - 1)).natDegree := by
        refine natDegree_add_le_of_le ?_ ?_
        exact Nat.le_refl y0_rep.natDegree
        have _ : (C a * X ^ (p - 1)).natDegree = (X ^ (p - 1) * C a).natDegree := by
          refine Eq.symm (Monic.natDegree_mul_comm ?_ (C a))
          exact monic_X_pow (p - 1)
        (expose_names; exact Nat.le_of_eq (id (Eq.symm h_4)))
      _ < p := by
        refine Nat.max_lt.mpr ?_
        constructor
        · (expose_names; exact Nat.lt_of_lt_of_eq h_pb_rep_y01_1 h_pbdim)
        · refine (Nat.le_sub_one_iff_lt ?_).mp ?_
          exact Nat.zero_lt_of_lt h_y0rep1
          apply Polynomial.natDegree_C_mul_X_pow_le a (p-1)
      _ = (minpoly F x).natDegree := by
        exact Nat.succ_inj.mp (congrArg Nat.succ (id (Eq.symm h_pbdim)))
    have h : y0p_rep = y1p_rep := by
      apply congruence_low_degree h3 h1 h2 (minpoly.monic h_int)
    exact Polynomial.ext_iff.mp h (p-1)
  have _: c^p - c = a := by
    calc
      c^p - c = y0p_rep.coeff (p-1) - c := by
        refine sub_left_inj.mpr ?_
        exact Eq.symm h_y0rep2
      _ = y1p_rep.coeff (p-1) - c := by
        exact sub_left_inj.mpr h_matchcoeff
      _ = y0_rep.coeff (p-1) + (Polynomial.X ^ (p-1) * Polynomial.C a).coeff (p-1) - c := by
        refine sub_left_inj.mpr ?_
        exact coeff_add y0_rep (X ^ (p - 1) * C a) (p - 1)
      _ = y0_rep.coeff (p-1) + a - c := by
        refine sub_left_inj.mpr ?_
        refine (add_right_inj (y0_rep.coeff (p - 1))).mpr ?_
        have h_moncoeff : ((monomial (p-1)) a).coeff (p-1) = if (p-1) = (p-1) then a else 0 := by
          apply Polynomial.coeff_monomial
        unfold monomial at h_moncoeff
        simp
      _ = c + a - c := sub_right_inj.mpr rfl
      _ = a := by ring
  have h_deg1 : (minpoly F x).natDegree ≤ 1 := by
    have _ : Fact (Nat.Prime p) := fact_iff.mpr hp
    have _ : CharP K p := by
      (expose_names; exact (Algebra.charP_iff F K p).mp h_2)
    let x1 := x - (algebraMap F K) c
    have fieldeq : x1^p = x1 := by
      calc
        x1^p = (x - (algebraMap F K) c)^p := by rfl
        _ = x^p - (algebraMap F K) c ^ p := sub_pow_char x ((algebraMap F K) c)
        _ = x + (algebraMap F K) a - (algebraMap F K) c ^ p := sub_left_inj.mpr h_rwx
        _ = x + (algebraMap F K) (c^p - c) - (algebraMap F K) c ^ p := by
          (expose_names;
            exact
              sub_left_inj.mpr
                (congrArg (HAdd.hAdd x) (congrArg (⇑(algebraMap F K)) (id (Eq.symm h_4)))))
        _ = x + (algebraMap F K) (c^p) - (algebraMap F K) c - (algebraMap F K) c ^ p := by
          have hsub : (algebraMap F K) (c^p - c) = (algebraMap F K) (c^p) - (algebraMap F K) c :=
            algebraMap.coe_sub (c ^ p) c
          rw [hsub]
          refine sub_left_inj.mpr ?_
          exact add_sub x ((algebraMap F K) (c ^ p)) ((algebraMap F K) c)
        _ = x + (algebraMap F K) c ^ p - (algebraMap F K) c - (algebraMap F K) c ^ p := by simp
        _ = x1 := by ring
    have hn : ∃ (n : ℤ), ↑n = x1 :=
      have h_bot : x1 ∈ (⊥ : Subfield K) := by
        exact (Subfield.mem_bot_iff_pow_eq_self K p).mpr fieldeq
      (mem_bot_iff_intCast p K).mp h_bot
    obtain ⟨n, hn⟩ := hn
    have _ : ∃ d : F, x = (algebraMap F K) d := by
      use (n + c)
      calc
      x = x1 + (algebraMap F K) c := Eq.symm (sub_add_cancel x ((algebraMap F K) c))
      _ = n + (algebraMap F K) c := by rw [← hn]
      _ = (algebraMap F K) n + (algebraMap F K) c := by
        refine (add_left_inj ((algebraMap F K) c)).mpr ?_
        exact Eq.symm (map_intCast (algebraMap F K) n)
      _ = (algebraMap F K) (n + c) := Eq.symm (algebraMap.coe_add (↑n) c)
    let pol1 := Polynomial.X - Polynomial.C (n + c)
    have _ : minpoly F x ∣ pol1 := by
      have _ : Polynomial.aeval x pol1 = 0 := by
        calc
        Polynomial.aeval x pol1 = Polynomial.aeval x (Polynomial.X - Polynomial.C (n + c)) := by rfl
        _ =  Polynomial.aeval x (Polynomial.X : Polynomial F) - Polynomial.aeval x (Polynomial.C (n + c)) := aeval_sub x
        _ = x - Polynomial.aeval x (Polynomial.C (n + c)) := by
          refine sub_left_inj.mpr ?_
          exact aeval_X x
        _ = x - (algebraMap F K) (n + c) := by
          refine sub_right_inj.mpr ?_
          exact aeval_C x (↑n + c)
        _ = x1 + (algebraMap F K) c - (algebraMap F K) (n + c) := by
          refine sub_left_inj.mpr ?_
          exact Eq.symm (sub_add_cancel x ((algebraMap F K) c))
        _ = 0 := by
          rw [← hn]
          simp
      (expose_names; exact minpoly.dvd_iff.mpr h_8)
    calc
      (minpoly F x).natDegree ≤ pol1.natDegree := by
        (expose_names; refine natDegree_le_of_dvd h_8 ?_)
        exact X_sub_C_ne_zero (↑n + c)
      _ = 1 := natDegree_X_sub_C (n+c)
      _ ≤ 1 := by exact NeZero.one_le
  have _ : 1 < 1 := by
    calc
      1 < p := Nat.Prime.one_lt hp
      p = aspol.natDegree := Eq.symm h_natdeg
      _ = (minpoly F x).natDegree := Eq.symm (natDegree_eq_of_degree_eq (congrArg degree ha))
      _ ≤ 1 := h_deg1
  simp_all
