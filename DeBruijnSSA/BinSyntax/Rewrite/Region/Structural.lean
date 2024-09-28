import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Product
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Distrib
import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural
import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Distrib
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Cast

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.packed {Γ Δ : Ctx α ε} {R : LCtx α} (r : Eqv φ Γ R) : Eqv φ ((Γ.pack, ⊥)::Δ) (R.pack::L)
  := r.packed_out.packed_in

def Eqv.unpacked {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ [(Γ.pack, ⊥)] [R.pack]) (h : Γ.Pure)
  : Eqv φ Γ R := r.unpacked_out.unpacked_in h

theorem Eqv.unpacked_out_unpacked_in {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ [(Γ.pack, ⊥)] [R.pack]} {h : Γ.Pure}
  : (r.unpacked_in h).unpacked_out = r.unpacked_out.unpacked_in h := by
  simp only [unpacked_in, unpacked_out_let1]
  induction r using Quotient.inductionOn
  simp only [Term.Eqv.packE_def', vwk_id_quot, unpacked_out_quot, let1_quot]
  rfl

theorem Eqv.unpacked_out_packed_in {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ Γ [R.pack]} : r.packed_in.unpacked_out = r.unpacked_out.packed_in (Δ := Δ) := by
  simp only [unpacked_out, packed_in, vsubst_lsubst]
  congr
  simp only [Subst.Eqv.unpack, unpack_def, InS.unpack, Set.mem_setOf_eq, csubst_quot,
    Term.Subst.Eqv.unpack, Subst.Eqv.vsubst_quot]
  congr; ext; simp

theorem Eqv.packed_out_unpacked_in {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ [(Γ.pack, ⊥)] R} {h : Γ.Pure}
  : (r.unpacked_in h).packed_out (L := L) = r.packed_out.unpacked_in h := by
  simp [
    unpacked_in, packed_out, let1_beta, vsubst_lsubst, vwk_id_eq_vwk, <-vsubst_fromWk,
    vsubst_vsubst
  ]

theorem Eqv.packed_out_packed_in {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ Γ R} : r.packed_in.packed_out (L := L) = r.packed_out.packed_in (Δ := Δ) := by
  simp [packed_in, packed_out, vsubst_lsubst]

theorem Eqv.packed_in_unpacked_app_out {Γ : Ctx α ε} {R L : LCtx α}
  {r : Eqv φ Γ [(R ++ L).pack]}
  : r.unpacked_app_out.packed_in (Δ := Δ) = r.packed_in.unpacked_app_out := by
  simp [unpacked_app_out, packed_in, vsubst_lsubst, unpacked_app_out]

theorem Eqv.packed_def' {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ Γ R} : r.packed (Δ := Δ) = r.packed_in.packed_out (L := L)
  := by simp [packed, packed_out_packed_in]

theorem Eqv.unpacked_def' {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ [(Γ.pack, ⊥)] [R.pack]} {h : Γ.Pure}
  : r.unpacked h = r.unpacked_out.unpacked_in h := by simp [unpacked, unpacked_out_unpacked_in]

theorem Eqv.packed_unpacked {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ [(Γ.pack, ⊥)] [R.pack]} {h : Γ.Pure} : (r.unpacked h).packed = r
  := by rw [unpacked, packed_def', packed_in_unpacked_in, packed_out_unpacked_out]

theorem Eqv.unpacked_packed {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ Γ R} {h : Γ.Pure} : r.packed.unpacked h = r
  := by rw [unpacked, packed_def', unpacked_out_packed_out, unpacked_in_packed_in]

@[simp]
theorem Eqv.vwk_slift_packed {Γ Δ Δ' : Ctx α ε} {R : LCtx α} {r : Eqv φ Γ R} {ρ : Δ'.InS Δ}
  : r.packed.vwk ρ.slift = r.packed (L := L) (Δ := Δ') := by simp [packed]

@[simp]
theorem Eqv.vwk_liftn₂_packed {Γ Δ Δ' : Ctx α ε} {R : LCtx α} {r : Eqv φ Γ R} {ρ : Δ'.InS Δ}
  : r.packed.vwk (ρ.liftn₂ (le_refl _) (le_refl V)) = r.packed (L := L)  (Δ := _::Δ') := by
  simp [<-Ctx.InS.lift_lift]

@[simp]
theorem Eqv.vwk1_packed {Γ Δ : Ctx α ε} {R : LCtx α} {r : Eqv φ Γ R}
  : r.packed.vwk1 (inserted := inserted) = r.packed (L := L)  (Δ := _::Δ) := by
  rw [vwk1, <-Ctx.InS.lift_wk0, vwk_slift_packed]

@[simp]
theorem Eqv.vwk2_packed {Γ Δ : Ctx α ε} {R : LCtx α} {r : Eqv φ Γ R}
  : r.packed.vwk2 (inserted := inserted) = r.packed (L := L) (Δ := head::_::Δ) := by
  rw [vwk2, <-Ctx.InS.lift_wk1, vwk_slift_packed]

@[simp]
theorem Eqv.vsubst_lift_packed {Γ Δ Δ' : Ctx α ε} {R : LCtx α} {r : Eqv φ Γ R}
  {σ : Term.Subst.Eqv φ Δ' Δ}
  : r.packed.vsubst (σ.lift (le_refl _)) = r.packed (L := L) (Δ := Δ') := by
  simp [packed]

@[simp]
theorem Eqv.vsubst_liftn₂_packed {Γ Δ Δ' : Ctx α ε} {R : LCtx α} {r : Eqv φ Γ R}
  {σ : Term.Subst.Eqv φ Δ' Δ}
  : r.packed.vsubst (σ.liftn₂ (le_refl _) (le_refl V)) = r.packed (L := L) (Δ := _::Δ') := by
  simp [<-Term.Subst.Eqv.lift_lift]

open Term.Eqv

theorem Eqv.packed_br {Γ : Ctx α ε} {L : LCtx α}
  {ℓ} {a : Term.Eqv φ Γ (A, ⊥)} {hℓ}
  : (br (L := L) ℓ a hℓ).packed (L := L)  (Δ := Δ) = ret ((a.packed.wk_res ⟨hℓ.get, by rfl⟩).inj) := by
  rw [packed, packed_out_br, packed_in_br, Term.Eqv.packed_of_inj, ret]
  congr
  induction a using Quotient.inductionOn
  apply Term.Eqv.eq_of_term_eq; rfl

theorem Eqv.packed_let1 {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A, e)} {r : Eqv φ ((A, ⊥)::Γ) R}
  : (let1 a r).packed (Δ := Δ) (L := L)
  = let1 a.packed (let1 (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)) r.packed) := by
  rw [packed, packed_out_let1, packed_in_let1, <-packed]

theorem Eqv.packed_let2 {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.prod B, e)} {r : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) R}
  : (let2 a r).packed (Δ := Δ) (L := L)
  = let2 a.packed (let1
    (pair (pair (var 2 (by simp)) (var 1 (by simp))) (var 0 Ctx.Var.shead))
    r.packed) := by
  rw [packed, packed_out_let2, packed_in_let2, <-packed]

theorem Eqv.packed_case {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.coprod B, e)} {r : Eqv φ ((A, ⊥)::Γ) R} {s : Eqv φ ((B, ⊥)::Γ) R}
  : (case a r s).packed (Δ := Δ) (L := L)
  = case a.packed
    (let1 (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)) r.packed)
    (let1 (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)) s.packed) := by
  simp only [packed, packed_out_case, packed_in_case]

theorem Eqv.packed_cfg_unpack {Γ : Ctx α ε} {L R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G}
  : (cfg R β G).packed (Δ := Δ)
  = letc R.pack
      β.packed.unpacked_app_out
      (unpack.lsubst (Subst.Eqv.fromFCFG (λi =>
        (let1 (pair (var 2 (by simp)) (var 0 Ctx.Var.shead)) (G i).packed.unpacked_app_out)))) := by
  rw [packed_def', packed_in_cfg, packed_out_cfg_letc_unpack, <-packed_def']
  congr; funext i
  rw [vwk1_unpacked_app_out, packed_out_let1, <-packed_def', <-unpacked_app_out_let1]
  simp

theorem Eqv.packed_cfg {Γ : Ctx α ε} {L R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G}
  : (cfg R β G).packed (Δ := Δ)
  = letc R.pack
      β.packed.unpacked_app_out
      (pack_coprod
        (λi => (let1 (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)) (G i).packed.unpacked_app_out)))
  := by
  rw [packed_def', packed_in_cfg, packed_out_cfg_letc, <-packed_def']
  congr; funext i
  rw [packed_out_let1, <-packed_def', unpacked_app_out_let1]

theorem Eqv.packed_cfg_split {Γ : Ctx α ε} {L R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G}
  : (cfg R β G).packed (Δ := Δ)
  = letc (Γ.pack.prod R.pack)
      (ret Term.Eqv.split ;; _ ⋊ β.packed.unpacked_app_out)
      (ret Term.Eqv.split ⋉ _ ;; assoc
        ;; _ ⋊ (ret Term.Eqv.distl_pack
          ;; pack_coprod (λi => acast R.get_dist
            ;; (G (i.cast R.length_dist)).packed.unpacked_app_out))) := by
  rw [packed, packed_out_cfg_letc, packed_in_letc_split]
  congr 3
  · rw [packed_in_unpacked_app_out, <-packed]
  · rw [packed_in_pack_coprod_arr]; congr; funext i; rw [packed_in_unpacked_app_out, <-packed]

theorem Eqv.packed_cfg_split_vwk1 {Γ : Ctx α ε} {L R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G}
  : (cfg R β G).packed (Δ := Δ)
  = letc (Γ.pack.prod R.pack)
      (ret Term.Eqv.split ;; _ ⋊ β.packed.unpacked_app_out)
      (ret Term.Eqv.split ⋉ _ ;; assoc
        ;; _ ⋊ (ret Term.Eqv.distl_pack
          ;; pack_coprod (λi => acast R.get_dist
            ;; (G (i.cast R.length_dist)).packed.unpacked_app_out))).vwk1 := by
  rw [packed_cfg_split]
  simp only [List.get_eq_getElem, Fin.coe_cast, vwk1_seq, vwk1_ltimes, vwk1_br, wk1_split,
    vwk1_rtimes, wk1_distl_pack, vwk1_pack_coprod, vwk1_acast, vwk1_unpacked_app_out, vwk1_packed]
  rfl

-- TODO: unpacked_app_out ltimes dinaturality

end Region

end BinSyntax
