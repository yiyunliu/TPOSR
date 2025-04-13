Require Import imports.
Require Export typing.
From Ltac2 Require Ltac2.
Set Default Proof Mode "Classic".
Ltac2 spec_refl () :=
  List.iter
    (fun a => match a with
           | (i, _, _) =>
               let h := Control.hyp i in
               try (specialize $h with (1 := eq_refl))
           end)  (Control.hyps ()).

Ltac spec_refl := ltac2:(Control.enter spec_refl).

Lemma subst_id b :  subst_tm (scons (var_tm var_zero) (funcomp var_tm shift)) b = b.
  symmetry. have h : b = subst_tm var_tm b by asimpl.
  rewrite {1}h.
  apply ext_tm.
  case => //=.
Qed.


Lemma here' : forall {A Γ T}, T = A ⟨shift⟩ ->  lookup 0 (A :: Γ) T.
Proof. move => > ->. by apply here. Qed.

Lemma there' : forall {n A Γ B T}, T = A ⟨shift⟩ ->
      lookup n Γ A -> lookup (S n) (B :: Γ) T.
Proof. move => > ->. by apply there. Qed.

Lemma WR_Conv Γ a b A B : Γ ⊢ a ▻ b ∈ A -> Γ ⊢ A ≡ B -> Γ ⊢ a ▻ b ∈ B.
Proof.
  move => + h. elim : A B / h; eauto with wt.
Qed.

Lemma WRs_Conv Γ a b A B : Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ A ≡ B -> Γ ⊢ a ▻+ b ∈ B.
Proof.
  move => h. move : B.
  elim : Γ a b A / h; qauto l:on use:WR_Conv db:wt.
Qed.

Lemma WR_Conv' Γ a b A B : Γ ⊢ a ▻ b ∈ A -> Γ ⊢ B ≡ A -> Γ ⊢ a ▻ b ∈ B.
Proof. move => > + /Equiv_sym; apply WR_Conv. Qed.

Lemma good_renaming_up ξ Γ Δ A :
  lookup_good_renaming ξ Γ Δ ->
  lookup_good_renaming (upRen_tm_tm ξ)  (A :: Γ) (A⟨ξ⟩ :: Δ).
Proof.
  rewrite /lookup_good_renaming => h.
  move => i B.
  inversion 1 =>*; subst.
  - apply here'. by asimpl.
  - asimpl. apply : there'; eauto. by asimpl.
Qed.

Lemma WR_App' Γ A A' i B B' M M' N N' T :
  T = B[N..] ->
  Γ ⊢ A ▻ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B' ∈ Univ i ->
  Γ ⊢ M ▻ M' ∈ Pi A B ->
  Γ ⊢ N ▻ N' ∈ A ->
  (* ------------------------ *)
  Γ ⊢ App B M N ▻ App B' M' N' ∈ T.
Proof. move =>> ->. apply WR_App. Qed.

Lemma WR_Beta' Γ A i B B' M M' N N' P T :
  P = M'[N'..] ->
  T = B[N..] ->
  Γ ⊢ A ▻ A ∈ Univ i ->
  A :: Γ ⊢ B ▻ B' ∈ Univ i ->
  A :: Γ ⊢ M ▻ M' ∈ B ->
  Γ ⊢ N ▻ N' ∈ A ->
  (*----------------------  *)
  Γ ⊢ App B (Lam A M) N ▻ P ∈ T.
Proof. move =>> -> ->. apply WR_Beta. Qed.

Lemma WR_Eta' Γ a b A A' i B B' u  :
  u = Lam A' (App B'⟨upRen_tm_tm shift⟩ b⟨shift⟩ (var_tm var_zero)) ->
  Γ ⊢ A ▻ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B' ∈ Univ i ->
  Γ ⊢ a ▻ b ∈  Pi A B ->
  Γ ⊢ a ▻ u ∈ Pi A B.
Proof. move => ->. apply WR_Eta. Qed.

Lemma wt_renaming_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ξ Δ,
        lookup_good_renaming ξ Γ Δ -> Wf Δ -> Δ ⊢ a⟨ξ⟩ ▻ b⟨ξ⟩ ∈ A⟨ξ⟩ ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> forall ξ Δ,
        lookup_good_renaming ξ Γ Δ -> Wf Δ -> Δ ⊢ a⟨ξ⟩ ▻+ b⟨ξ⟩ ∈ A⟨ξ⟩ ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind=>//; eauto with wt.
  - hauto lq:on unfold:lookup_good_renaming db:wt.
  - hauto q:on db:wt.
  - hauto q:on use:good_renaming_up db:wt.
  - hauto q:on use:good_renaming_up db:wt.
  - move => */=. apply : WR_App'; eauto; eauto using good_renaming_up with wt.
    by asimpl.
  - move => *. apply : WR_Beta';
      (* The two eautos is *NOT* a typo. Need to suppress the use of
      wt constructors to avoid prematurely instantiating ▻+ with the
      One constructor *)
      eauto using good_renaming_up;
      eauto using good_renaming_up with wt.
    by asimpl.
    rewrite -/ren_tm.
    by asimpl.
  - move => Γ a b A A' i B B' hA ihA hB ihB ha iha ξ Δ hξ hΔ /=.
    apply : WR_Eta'; eauto; eauto using good_renaming_up with wt; cycle 1.
    by asimpl.
Qed.

Lemma wt_renaming :
  forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ξ Δ,
      lookup_good_renaming ξ Γ Δ -> Wf Δ -> Δ ⊢ a⟨ξ⟩ ▻ b⟨ξ⟩ ∈ A⟨ξ⟩ .
Proof. hauto l:on use:wt_renaming_mutual. Qed.

Lemma wt_renaming_univ :
  forall Γ a b i, Γ ⊢ a ▻ b ∈ Univ i -> forall ξ Δ,
      lookup_good_renaming ξ Γ Δ -> Wf Δ -> Δ ⊢ a⟨ξ⟩ ▻ b⟨ξ⟩ ∈ Univ i.
Proof. hauto l:on use:wt_renaming. Qed.

Definition lookup_good_morphing ρ Γ Δ :=
  forall n A, lookup n Γ A -> Δ ⊢ ρ n ▻ ρ n ∈ A[ρ].

Lemma lookup_good_renaming_shift A Δ:
  lookup_good_renaming shift Δ (A :: Δ).
Proof. rewrite /lookup_good_renaming => >. apply there. Qed.

Lemma subst_ren_factor A ρ ξ :  A[funcomp (ren_tm ξ) ρ] = A[ρ]⟨ξ⟩.
Proof. by asimpl. Qed.

Lemma good_morphing_up ρ k Γ Δ A B
  (h : lookup_good_morphing ρ Γ Δ) :
  Δ ⊢ A[ρ] ▻ B ∈ Univ k ->
  lookup_good_morphing (up_tm_tm ρ) (A :: Γ) (A [ρ] :: Δ).
Proof.
  rewrite /lookup_good_morphing => h1.
  inversion 1=>*; subst.
  - apply WR_Var => /=.
    + eauto with wt.
    + asimpl. apply : here'. by asimpl.
  - asimpl. rewrite !subst_ren_factor.
    eapply wt_renaming_mutual. hauto l:on unfold:lookup_good_morphing.
    apply lookup_good_renaming_shift.
    eauto with wt.
Qed.

Lemma wt_morphing_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻ b[ρ] ∈ A[ρ] ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻+ b[ρ] ∈ A[ρ] ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind=>//; eauto with wt.
  - hauto q:on db:wt.
  - hauto q:on use:good_morphing_up db:wt.
  - hauto q:on use:good_morphing_up db:wt.
  - move => *.
    apply : WR_App'; eauto. rewrite -/subst_tm.
    by asimpl. qauto l:on use:good_morphing_up db:wt.
  - move => Γ A i  B B' M M' N N' hA ihA hB ihB hM ihM hN ihN ρ Δ hρ hΔ /=.
    apply : WR_Beta'; eauto; cycle 1.
    by asimpl.
    hauto lq:on use:good_morphing_up db:wt.
    hauto lq:on use:good_morphing_up db:wt.
    by asimpl.
  - move => Γ a b A A' i B B' hA ihA hB ihB ha iha ρ Δ hρ hΔ /=.
    apply : WR_Eta'; eauto using good_morphing_up with wt; cycle 1.
    apply ihB. hauto lq:on use:good_morphing_up db:wt.
    hauto lq:on use:good_morphing_up db:wt.
    by asimpl.
Qed.

Lemma wt_morphing :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻ b[ρ] ∈ A[ρ] ).
Proof. sfirstorder use:wt_morphing_mutual. Qed.

Lemma wt_morphing_univ  :
  (forall Γ a b i, Γ ⊢ a ▻ b ∈ Univ i -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻ b[ρ] ∈ Univ i ).
Proof. hauto lq:on use:wt_morphing. Qed.

Lemma equiv_renaming Γ A B (h : Γ ⊢ A ≡ B) :
  forall ξ Δ, lookup_good_renaming ξ Γ Δ -> ⊢ Δ -> Δ ⊢ A⟨ξ⟩ ≡ B⟨ξ⟩.
Proof.
  elim : A B / h; hauto q:on ctrs:WtEquiv use:wt_renaming_mutual.
Qed.

Lemma wr_morphing :
  forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻ b[ρ] ∈ A[ρ].
Proof. apply wt_morphing_mutual. Qed.

Lemma equiv_morphing Γ Δ A B ρ (h : Γ ⊢ A ≡ B) :
  lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ A[ρ] ≡ B[ρ].
Proof.
  move : Δ ρ.
  elim : A B/h.
  - hauto lq:on ctrs:WtEquiv use:wt_morphing_univ.
  - hauto lq:on ctrs:WtEquiv use:wt_morphing_univ.
  - hauto lq:on ctrs:WtEquiv use:wt_morphing_univ.
Qed.

Lemma wrs_Equiv Γ A B i (h : Γ ⊢ A ▻+ B ∈ Univ i) : Γ ⊢ A ≡ B.
Proof.
  move E : (Univ i) h => T h.
  move : E.
  elim : A B T / h;
    hauto lq:on ctrs:WtEquiv.
Qed.

Lemma Conv_Equiv Γ A B C i :
  Γ ⊢ A ▻+ B ∈ Univ i ->
  Γ ⊢ A ▻+ C ∈ Univ i ->
  Γ ⊢ B ≡ C.
Proof.
  move => /wrs_Equiv /Equiv_sym + /wrs_Equiv.
  apply WE_Trans.
Qed.

Lemma Wt_Wf_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> ⊢ Γ ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> ⊢ Γ) /\
  (forall Γ, ⊢ Γ -> True).
Proof. apply wt_mutual_ind; eauto with wt. Qed.

Lemma Wf_cons_inv A Γ :
  ⊢ A :: Γ ->
  ⊢ Γ /\ exists B i, Γ ⊢ A ▻ B ∈ Univ i.
Proof. hauto l:on inv:Wf use:Wt_Wf_mutual. Qed.

Lemma lookup_good_id A A' Γ
  (h0 : ⊢ A' :: Γ)
  (h : Γ ⊢ A' ≡ A) :
  lookup_good_morphing var_tm (A :: Γ) (A' :: Γ).
Proof.
  move => k T.
  elim /lookup_inv => _.
  + move => ? ? ? []*. subst. asimpl.
    apply WR_Conv with (A := A' ⟨shift⟩).
    hauto q:on ctrs:WtRed, lookup.
    renamify.
    apply : equiv_renaming=>//; last by apply lookup_good_renaming_shift. exact h.
  + move => n A1 Γ0 B0 ? ? []*. subst.
    asimpl. renamify.
    change (var_tm (S n)) with ((var_tm n)⟨shift⟩).
    eapply wt_renaming_mutual=>//; last by apply lookup_good_renaming_shift.
    apply : WR_Var; eauto.
    sfirstorder use:Wf_cons_inv.
Qed.

Lemma Ctx_conv A B Γ M N C (h : A :: Γ ⊢ M ▻ N ∈ C) (h1 : Γ ⊢ A ≡ B)
  (h2 : ⊢ B :: Γ) :
  B :: Γ ⊢ M ▻ N ∈ C.
Proof.
  move /wr_morphing /(_ var_tm) : h. asimpl. apply=>//.
  apply lookup_good_id; eauto.
  move : h1. apply Equiv_sym.
Qed.

Lemma WRs_Ctx_conv A B Γ M N C (h : A :: Γ ⊢ M ▻+ N ∈ C) (h1 : Γ ⊢ A ≡ B)
  (h2 : ⊢ B :: Γ) :
  B :: Γ ⊢ M ▻+ N ∈ C.
Proof.
  move /(proj1 (proj2 wt_morphing_mutual)) /(_ var_tm) : h. asimpl. apply=>//.
  apply lookup_good_id; eauto.
  move : h1. apply Equiv_sym.
Qed.

Lemma lh_refl_helper Γ A0 A i B :
  Γ ⊢ A0 ▻+ A ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  Γ ⊢ Pi A0 B ▻+ Pi A B ∈ Univ i.
Proof.
  move E : (Univ i) => T h.
  move : i E.
  elim : Γ A0 A T / h.
  - move => Γ A0 A ? h i ? hB; subst.
    have ? : ⊢ A0 :: Γ by eauto with wt.
    apply WRs_One.
    apply : WR_Prod=>//.
    apply : Ctx_conv; eauto with wt.
  - move => Γ A A0 A1 T h0 h1 ih i ? h2. subst.
    specialize ih with (1 := eq_refl).
    move /ih : (h2) {ih}.
    apply : WRs_Trans.
    apply WR_Prod; eauto.
    apply : Ctx_conv; eauto with wt.
    hauto lq:on rew:off use:wrs_Equiv, Equiv_sym db:wt.
Qed.

Lemma lh_refl_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> Γ ⊢ a ▻ a ∈ A ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ a ▻ a ∈ A ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind=>//; eauto with wt.
Qed.

Definition lookup_good_morphing2 ρ0 ρ1 Γ Δ :=
  forall n A, lookup n Γ A -> Δ ⊢ ρ0 n ▻ ρ1 n ∈ A[ρ0].

Lemma good_morphing2_up ρ0 ρ1 A B k Γ Δ
  (h : lookup_good_morphing2 ρ0 ρ1 Γ Δ) :
  Δ ⊢ A[ρ0] ▻ B ∈ Univ k ->
  lookup_good_morphing2 (up_tm_tm ρ0) (up_tm_tm ρ1) (A :: Γ) (A[ρ0] :: Δ).
Proof.
  rewrite /lookup_good_morphing => h1.
  inversion 1=>*; subst.
  - apply WR_Var => /=.
    + eauto with wt.
    + asimpl. apply : here'. by asimpl.
  - asimpl. rewrite !subst_ren_factor.
    eapply wt_renaming_mutual. hauto l:on unfold:lookup_good_morphing.
    apply lookup_good_renaming_shift.
    eauto with wt.
Qed.

Lemma lookup_good_morphing2_lh_refl ρ0 ρ1 Γ Δ :
  lookup_good_morphing2 ρ0 ρ1 Γ Δ ->
  lookup_good_morphing2 ρ0 ρ0 Γ Δ.
Proof.
  hauto lq:on use:lh_refl_mutual unfold:lookup_good_morphing2.
Qed.

Lemma wt_morphing2_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ρ0 ρ1 Δ,
        lookup_good_morphing2 ρ0 ρ1 Γ Δ -> Wf Δ -> Δ ⊢ a[ρ0] ▻ b[ρ1] ∈ A[ρ0] ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> forall ρ0 ρ1 Δ,
        lookup_good_morphing2 ρ0 ρ1 Γ Δ -> Wf Δ -> Δ ⊢ a[ρ0] ▻+ b[ρ1] ∈ A[ρ0] ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind; eauto with wt.
  - hauto q:on db:wt.
  - hauto q:on use:good_morphing2_up db:wt.
  - hauto q:on use:lookup_good_morphing2_lh_refl, good_morphing2_up db:wt.
  - move => */=.
    apply : WR_App'; eauto. by asimpl. qauto l:on use:good_morphing2_up db:wt.
  - move => Γ A i B B' M M' N N' hA ihA hB ihB hM ihM hN ihN ρ0 ρ1 Δ hρ hΔ /=.
    eapply WR_Beta' with (M' := M'[up_tm_tm ρ1]) (N' := N'[ρ1]) (i := i); eauto 3.
    + by asimpl.
    + by asimpl.
    + qauto l:on db:wt use:lh_refl_mutual.
    (* + sfirstorder use:lookup_good_morphing2_lh_refl. *)
    (* + sfirstorder use:lookup_good_morphing2_lh_refl. *)
    + hauto lq:on use:good_morphing2_up, lookup_good_morphing2_lh_refl db:wt.
    + hauto lq:on use:good_morphing2_up, lookup_good_morphing2_lh_refl db:wt.
  - move => Γ a b A A' i B B' hA ihA hB ihB ha iha ρ0 ρ1 Δ hρ hΔ /=.
    apply : WR_Eta'; eauto; cycle 1.
    qauto l:on use:good_morphing2_up db:wt.
    by asimpl.
  - qauto l:on use:lookup_good_morphing2_lh_refl, WR_Conv db:wt.
  - qauto l:on use:lookup_good_morphing2_lh_refl, WR_Conv db:wt.
  - eauto using lookup_good_morphing2_lh_refl with wt.
Qed.

Lemma WR_cong Γ A B B' T M M' :
  A :: Γ ⊢ B ▻ B' ∈ T ->
  Γ ⊢ M ▻ M' ∈ A ->
  Γ ⊢ B[M..] ▻ B'[M'..] ∈ T[M..].
Proof.
  move => + h.
  move /(proj1 wt_morphing2_mutual).
  apply; last by sfirstorder use:Wt_Wf_mutual.
  move => k A0.
  elim /lookup_inv=>_.
  - move => ? ? ? []*. subst. by asimpl.
  - move => n A1 Γ0 B0 ? ? []*. subst.
    asimpl. hauto lq:on use:Wt_Wf_mutual db:wt.
Qed.

(* This lemma is silly but I really need it because otherwise
automation gets blocked too easily *)
Lemma WR_cong_univ Γ A B B' i M M' :
  A :: Γ ⊢ B ▻ B' ∈ Univ i ->
  Γ ⊢ M ▻ M' ∈ A ->
  Γ ⊢ B[M..] ▻ B'[M'..] ∈ Univ i.
Proof. apply WR_cong. Qed.

Lemma rh_refl_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> Γ ⊢ b ▻ b ∈ A ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ b ▻ b ∈ A ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind; eauto with wt.
  - eauto using Ctx_conv with wt.
  - move => *.
    apply : WR_Conv; eauto with wt.
    hauto lq:on use:Ctx_conv db:wt.
  - move => Γ A A' i B B' M M' N N' hA ihA hB ihB hM ihM hN ihN.
    apply : WR_Conv; eauto with wt.
    apply : WR_App; eauto with wt.
    eauto using Ctx_conv with wt.
    apply : WE_Exp.
    apply /WR_cong : hB hN.
  - move => Γ A i B B' M M' N N' hA ihA hB ihB hM ihM hN ihN.
    apply : WR_Conv.
    apply : WR_cong; eauto.
    apply : WE_Exp.
    eapply lh_refl_mutual in hB.
    apply /WR_cong : hB hN.
  - move => Γ a b A A' i B B' hA ihA hB ihB ha iha /=.
    apply : WR_Conv; eauto; eauto with wt.
    apply : WR_Lam; eauto; eauto using Ctx_conv with wt.
    have ? : ⊢ A' :: Γ by hauto lq:on db:wt.
    have ? : ⊢ A :: Γ by hauto lq:on db:wt.
    have ? : ⊢ A' ⟨ shift ⟩ :: A' :: Γ by hauto use:wt_renaming_univ, lookup_good_renaming_shift lq:on db:wt.
    apply : WR_App'; eauto.
    have hE : B' = subst_tm ids B' by asimpl.
    asimpl.
    rewrite {1}hE.
    apply ext_tm. case => //=.
    eapply wt_renaming_univ. apply ihA. by eauto using lookup_good_renaming_shift.
    by eauto.
    apply : wt_renaming_univ; cycle 1. eauto using lookup_good_renaming_shift, good_renaming_up.
    eauto.
    apply : Ctx_conv; eauto with wt.
    set U := Pi _ _. change U with (Pi A' B')⟨shift⟩.
    apply : wt_renaming; eauto with wt. apply lookup_good_renaming_shift.
    apply WR_Var; eauto. apply here.
Qed.

Lemma lookup_wf Γ n A (h : ⊢ Γ) (h0 : lookup n Γ A) : exists i, Γ ⊢ A ▻ A ∈ Univ i.
Proof.
  move : h.
  elim : n Γ A / h0.
  - move => A Γ /Wf_cons_inv.
    move => [h0][B][i]h1.
    exists i.
    move /(proj1 lh_refl_mutual) : (h1).
    move/(proj1 wt_renaming_mutual).
    apply. by apply lookup_good_renaming_shift.
    by apply /Wf_cons : h1.
  - move => n A Γ B h ih /Wf_cons_inv.
    move => [/ih+][B0][i]h1.
    move => [j]h2.
    exists j.
    move/(proj1 wt_renaming_mutual) : h2.
    apply. by apply lookup_good_renaming_shift.
    apply /Wf_cons : h1.
Qed.

Lemma Univ_inv Γ i N T (h : Γ ⊢ Univ i ▻ N ∈ T) :
  N = Univ i /\ Γ ⊢ T ≡ Univ (S i).
Proof.
  move E : (Univ i) h => M h.
  move : i E.
  elim : Γ M N T / h=>//; try hauto lq:on rew:off db:wt.
  move => Γ a b A A' i B B' hA ihA hB ihB ha iha i0 ?. subst.
  specialize iha with (1 := eq_refl).
  move : iha => [? hU]. subst.
  (* Impossible by lambda FP *)
  admit.
Admitted.

Lemma Var_inv Γ n N T (h : Γ ⊢ var_tm n ▻ N ∈ T) :
  exists A, lookup n Γ A /\ Γ ⊢ T ≡ A.
Proof.
  move E : (var_tm n) h => M h.
  move : n E.
  elim : Γ M N T / h=>//.
  - hauto lq:on use:lookup_wf db:wt.
  - hauto lq:on rew:off db:wt.
  - hauto lq:on rew:off db:wt.
Qed.


Lemma Prod_inv Γ A B N T (h : Γ ⊢ Pi A B ▻ N ∈ T) :
  exists A' B' i, N = Pi A' B' /\ Γ ⊢ A ▻ A' ∈ Univ i /\ A::Γ ⊢ B ▻ B' ∈ Univ i /\ Γ ⊢ T ≡ Univ i.
Proof.
  move E : (Pi A B) h => M h.
  move : A B E.
  elim : Γ M N T / h=>//.
  - hauto lq:on use:Wt_Wf_mutual db:wt.
  - move => Γ a b A A' i B B' hA _ hB _ ha iha A0 B0 ?. subst.
    spec_refl.
    move : iha => [A1][B1][i0][?][ihA][ihB]hU. subst.
    (* hU should lead to a contradiction by noconfusion *)
    admit.
  - hauto lq:on rew:off db:wt.
  - hauto lq:on rew:off db:wt.
Admitted.

Lemma Lam_inv Γ A M N T (h : Γ ⊢ Lam A M ▻ N ∈ T) :
  exists A' M' B i,
    (* N = Lam A' M' /\ *)
    Γ ⊢ A ▻ A' ∈ Univ i /\
    A::Γ ⊢ B ▻ B ∈ Univ i /\
    A::Γ ⊢ M ▻ M' ∈ B /\
    Γ ⊢ T ≡ Pi A B.
Proof.
  move E : (Lam A M) h => M0 h.
  move : A M E.
  elim : Γ M0 N T / h=>//.
  - hauto lq:on use:Wt_Wf_mutual db:wt.
  - hauto lq:on rew:off db:wt.
  - hauto lq:on rew:off db:wt.
Qed.

Lemma App_inv Γ P B Q N T (h : Γ ⊢ App B P Q ▻ N ∈ T) :
  exists A A' B' Q' i,
    Γ ⊢ A ▻ A' ∈ Univ i /\ A::Γ ⊢ B ▻B' ∈ Univ i /\ Γ ⊢ Q ▻ Q' ∈ A /\
    Γ ⊢ T ≡ B[Q..] /\
    (* App case *)
    ((exists P', Γ ⊢ P ▻ P' ∈ Pi A B) \/
    (* Beta case *)
     (exists A0 A'' R R', P = Lam A R /\ A::Γ ⊢ R ▻ R' ∈ B /\
                         Γ ⊢ A0 ▻+ A'' ∈ Univ i /\ Γ ⊢ A0 ▻+ A ∈ Univ i)).
Proof.
  move E : (App B P Q) h => M h.
  move : B P Q E.
  elim : Γ M N T / h=>//.
  - move => Γ A A' i B B' M M' N N' hA _ hB _ hM _ hN _ >[]*. subst.
    exists A, A', B', N', i.
    repeat split => //.
    (* Factor out the first bullet *)
    + apply : WE_Red.
      move /WR_cong: hB hN. repeat move/[apply].
      apply /(proj1 lh_refl_mutual).
    + sfirstorder.
  - move => Γ A i B B' M M' N N' hA _ hB _ hM _ hN _ > []*.
    subst. exists A, A, B, N', i.
    repeat split => //.
    (* Factor out the first bullet *)
    + by eapply lh_refl_mutual in hB.
    + apply : WE_Red.
      move /WR_cong: hB hN. repeat move/[apply].
      apply /(proj1 lh_refl_mutual).
    + qauto use:lh_refl_mutual,WR_Lam.
  - hauto lq:on rew:off db:wt.
  - hauto lq:on rew:off db:wt.
Qed.

Lemma lookup_deter n Γ A A' : lookup n Γ A -> lookup n Γ A' -> A = A'.
Proof. move => h. move : A'. elim : n Γ A /h => //=; hauto lq:on inv:lookup. Qed.

Reserved Notation "Γ ⊢ a ≃ b ∈  A" (at level 70, no associativity).


Lemma unique_sorts_mutual :
  forall Γ a b c A, Γ ⊢ a ▻ b ∈ A -> forall i j, A = Univ i -> Γ ⊢ a ▻ c ∈ Univ j -> i = j.
Admitted.

(* Lemma Prod_functionality Γ A B0 B1 i : *)


Lemma Prod_cong_stage0 Γ A0 A i B :
  Γ ⊢ A0 ▻+ A ∈ Univ i ->
  A0 :: Γ ⊢ B ▻ B ∈ Univ i ->
  Γ ⊢ Pi A0 B ▻+ Pi A B ∈ Univ i.
Proof.
  move => h h1.
  suff : A :: Γ ⊢ B ▻ B ∈ Univ i by sfirstorder use:lh_refl_helper.
  apply Ctx_conv with (A := A0); eauto with wt.
  apply /wrs_Equiv : h.
  hauto lq:on use:rh_refl_mutual db:wt.
Qed.

(* Lemma Prod_cong' A Γ :  *)
(*   A :: Γ ⊢ B ≡ B0 -> *)
(*   Γ ⊢ Pi A B ≡ Pi A B0. *)

Lemma Univ_Inj Γ i j :
  Γ ⊢ Univ i ≡ Univ j -> i = j.
Admitted.

Lemma Prod_cong Γ A A' B B' i :
  Γ ⊢ A ▻+ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻+ B' ∈ Univ i ->
  Γ ⊢ Pi A B ▻+ Pi A' B' ∈ Univ i.
Proof.
  move E : (A :: Γ) => Δ.
  move E0 : (Univ i) => T + h.
  move : A Γ i E E0.
  elim : Δ B B' T / h.
  - move => Γ M N A h A0 Γ0 i ? ? h1. subst.
    have : Γ0 ⊢ Pi A0 M ▻ Pi A0 N ∈ Univ i by
      hauto lq:on use:lh_refl_mutual db:wt.
    move / WRs_Trans. apply.
    apply Prod_cong_stage0; eauto. sfirstorder use:rh_refl_mutual.
  - move => Γ M N P A hM hN ih A0 Γ0 i ? ? h. subst.
    specialize ih with (1 := eq_refl) (2 := eq_refl) (3 := h).
    move /WRs_Trans : ih. apply.
    hauto lq:on use:lh_refl_mutual db:wt.
Qed.

Lemma equiv_cast Γ i A B :
  Γ ⊢ A ▻ A ∈ Univ i ->
  Γ ⊢ A ≡ B ->
  Γ ⊢ B ▻ B ∈ Univ i.
Proof.
  move => + h.
  elim : A B / h.
  - move => A B i0 h0 h1.
    have ? : i0 = i by sfirstorder use:unique_sorts_mutual. subst.
    sfirstorder use:rh_refl_mutual.
  - move => A B i0 h0 h1.
    have ? : i0 = i by hauto lq:on rew:off use:unique_sorts_mutual, rh_refl_mutual. subst.
    sfirstorder use:lh_refl_mutual.
  - eauto.
Qed.

Inductive WtEquivHom Γ i : tm -> tm -> Prop :=
| WEH_Red A B  :
  Γ ⊢ A ▻ B ∈ Univ i ->
  (* ------------------- *)
  Γ ⊢ A ≃ B ∈ i
| WEH_Exp A B  :
  Γ ⊢ B ▻ A ∈ Univ i ->
  (* ------------------- *)
  Γ ⊢ A ≃ B ∈ i
| WEH_Trans A B C :
  Γ ⊢ A ≃ B ∈ i ->
  Γ ⊢ B ≃ C ∈ i ->
  Γ ⊢ A ≃ C ∈ i
where
"Γ ⊢ A ≃ B ∈ i" := (WtEquivHom Γ i A B ).

Lemma WtEquivHom_embed Γ i A B :
  Γ ⊢ A ≃ B ∈ i ->
  Γ ⊢ A ≡ B.
Proof. induction 1; hauto lq:on ctrs:WtEquiv. Qed.

Lemma WtEquivHom_regularity Γ i A B :
  Γ ⊢ A ≃ B ∈ i -> Γ ⊢ A ▻ A ∈ Univ i /\ Γ ⊢ B ▻ B ∈ Univ i.
  induction 1; sfirstorder use:lh_refl_mutual, rh_refl_mutual. Qed.

Lemma equiv_cast' Γ i A C B :
  Γ ⊢ A ▻ C ∈ Univ i ->
  Γ ⊢ A ≡ B ->
  Γ ⊢ A ≃ B ∈ i.
Proof.
  move => + h.
  move : C.
  elim : A B  /h.
  - move => A B i0 h0 h1 C.
    have ? : i0 = i by hauto lq:on use:unique_sorts_mutual, lh_refl_mutual.
    hauto lq:on ctrs:WtEquivHom.
  - move => A B i0 h0 h1 C.
    have ? : i0 = i by hauto lq:on use:unique_sorts_mutual, lh_refl_mutual, rh_refl_mutual.
    hauto lq:on ctrs:WtEquivHom.
  - move => A B C h0 ih0 h1 ih1 C0 {}/ih0 ih0.
    have {}/ih1 : Γ ⊢ B ▻ B ∈ Univ i by hauto l:on use:WtEquivHom_regularity.
    eauto using WEH_Trans.
Qed.

Lemma Prod_cong' Γ A _A i B0 B1 :
  Γ ⊢ A ▻ _A ∈ Univ i ->
  A :: Γ ⊢ B0 ≃ B1 ∈ i ->
  Γ ⊢ Pi A B0 ≃ Pi A B1 ∈ i.
Proof.
  move => h h0.
  elim : B0 B1 / h0.
  - move => B0 B1 hB.
    apply WEH_Red.
    constructor; sfirstorder use:lh_refl_mutual.
  - move => B0 B1 hB.
    apply WEH_Exp.
    constructor; sfirstorder use:rh_refl_mutual, lh_refl_mutual.
  - hauto lq:on ctrs:WtEquivHom.
Qed.

Lemma unique_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall B, Γ ⊢ a ▻ a ∈ B -> Γ ⊢ A ≡ B ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> forall B, Γ ⊢ a ▻ a ∈ B -> Γ ⊢ A ≡ B ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind.
  - move => Γ n A hΓ _ hn B.
    move /Var_inv.
    hauto lq:on use:lookup_deter, Equiv_sym.
  - move => Γ i hΓ _ B.
    move /Univ_inv => [_ hB]. eauto using Equiv_sym.
  - move => Γ i A A' B B' hA ihA hB ihB U.
    move /Prod_inv.
    move => [A'0][B'0][j][[? ?]][hA0][hB0]hU.
    eapply lh_refl_mutual in hA0, hB0. apply ihB in hB0.
    (* By injectivity of universe. Also provable through lambdaFP *)
    have ? : j = i by hauto lq:on use:Univ_Inj. subst.
    by apply Equiv_sym.
  - move => Γ A A' i B M M' hA ihA hB ihB hM ihM U.
    move /Lam_inv.
    move => [A'0][M'0][B0][i0][hA0][hB0][hM0]hE.
    eapply lh_refl_mutual in hM0. apply ihM in hM0 => {ihM}.
    apply Equiv_sym in hE. apply : WE_Trans; eauto. clear hE.
    apply Equiv_sym in hM0.
    have {}hM0 : A :: Γ ⊢ B0 ≃ B ∈ i0 by sfirstorder use:equiv_cast', Equiv_sym.
    apply Equiv_sym.
    apply : WtEquivHom_embed; eauto.
    apply : Prod_cong'; eauto.
  - move => Γ A A' i B B' M M' N N' hA ihA hB ihB hM ihM hN ihN U.
    move /App_inv. move => [A0][A0'][B0][N1][i0][hA0][hB0][hN'][hu]_.
    by apply Equiv_sym.
  - hauto lq:on use:App_inv, Equiv_sym.
  - by eauto.
  - hauto lq:on db:wt.
  - hauto lq:on db:wt.
  - hauto lq:on db:wt.
  - hauto lq:on db:wt.
  - done.
  - done.
Qed.

Lemma exchange Γ a b c A0 A1 :
  Γ ⊢ a ▻ b ∈ A0 ->
  Γ ⊢ a ▻ c ∈ A1 ->
  Γ ⊢ a ▻ b ∈ A1.
Proof.
  move => h0 h1. apply : WR_Conv; eauto.
  hauto lq:on use:unique_mutual, lh_refl_mutual.
Qed.

Lemma exchange_multi_step Γ a b c A0 A1 :
  Γ ⊢ a ▻+ b ∈ A0 ->
  Γ ⊢ a ▻ c ∈ A1 ->
  Γ ⊢ a ▻+ b ∈ A1.
Proof.
  move => h0 h1. apply : WRs_Conv; eauto.
  hauto lq:on use:unique_mutual, lh_refl_mutual.
Qed.

Lemma Lam_cong Γ A A' M M' B C i :
  Γ ⊢ A ▻+ A' ∈ Univ i ->
  A :: Γ ⊢ M ▻+ M' ∈ B ->
  A :: Γ ⊢ B ▻ C ∈ Univ i ->
  Γ ⊢ Lam A M ▻+ Lam A' M' ∈ Pi A B.
Proof.
  move E : (A :: Γ) => Δ + h.
  move : A Γ E A' C i.
  elim : Δ M M' B / h.
  - move => Γ M N B h A0 Γ0 ? A' C i h0 h1. subst.
    have : Γ0 ⊢ Lam A0 M ▻ Lam A0 N ∈ Pi A0 B by
      hauto lq:on use:lh_refl_mutual db:wt.
    move /WRs_Trans. apply.
    move E : (Univ i) h0 =>T h0.
    move : i E h h1.
    elim : Γ0 A0 A' T / h0.
    + move => Γ A0 A1 ? h i ? h0 h1; subst.
      apply : WRs_One.
      apply : WR_Lam; eauto; sfirstorder use:lh_refl_mutual, rh_refl_mutual.
    + move => Γ A0 A1 A2 ? h0 h1 ih i ? h2 h3. subst.
      move => [:tr0].
      apply WRs_Trans with (N := Lam A1 N).
      abstract : tr0.
      qauto l:on use:lh_refl_mutual, rh_refl_mutual db:wt.
      specialize ih with (1 := eq_refl).
      move /Ctx_conv in h2.
      move /Ctx_conv in h3.
      have h4 : Γ ⊢ A0 ≡ A1 by qauto l:on db:wt.
      have h5 : ⊢ A1 :: Γ by qauto l:on inv:WtReds db:wt.
      move /(_ _ h4 h5) in h2.
      move /(_ _ h4 h5) in h3.
      move /(_ h2 h3) : ih.
      eapply rh_refl_mutual in tr0.
      move => ih.
      eapply WRs_Conv; eauto.
      sfirstorder use:unique_mutual.
  - move => Γ M N P A hM hN ih A0 Γ0 ? A' C i h0 h1; subst.
    specialize ih with (1 := eq_refl) (2 := h0) (3 := h1).
    apply : WRs_Trans; last by exact ih.
    qauto l:on use:lh_refl_mutual db:wt.
Qed.

Lemma wr_lh_refl :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> Γ ⊢ a ▻ a ∈ A ).
Proof. exact (proj1 lh_refl_mutual). Qed.

Lemma wrs_lh_refl :
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ a ▻ a ∈ A ).
Proof. exact (proj1 (proj2 lh_refl_mutual)). Qed.

Lemma wr_rh_refl :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> Γ ⊢ b ▻ b ∈ A ).
Proof. exact (proj1 rh_refl_mutual). Qed.

Lemma wrs_rh_refl :
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ b ▻ b ∈ A ).
Proof. exact (proj1 (proj2 rh_refl_mutual)). Qed.

#[export]Hint Resolve wr_lh_refl wrs_lh_refl wr_rh_refl wrs_rh_refl : wt.

Lemma Ctx_step A B i Γ M N C (h : A :: Γ ⊢ M ▻ N ∈ C) (h1 : Γ ⊢ A ▻ B ∈ Univ i) :
  B :: Γ ⊢ M ▻ N ∈ C.
Proof.
  apply : Ctx_conv; eauto with wt.
Qed.

Lemma WRs_Ctx_step A B i Γ M N C (h : A :: Γ ⊢ M ▻+ N ∈ C) (h1 : Γ ⊢ A ▻ B ∈ Univ i) :
  B :: Γ ⊢ M ▻+ N ∈ C.
Proof.
  apply : WRs_Ctx_conv; eauto with wt.
Qed.


#[export]Hint Resolve Ctx_step : wt.

Lemma App_cong Γ A A' i B B' M M' N N' :
  Γ ⊢ A ▻+ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻+ B' ∈ Univ i ->
  Γ ⊢ M ▻+ M' ∈ Pi A B ->
  Γ ⊢ N ▻+ N' ∈ A ->
  Γ ⊢ App B M N ▻+ App B' M' N' ∈ B[N..].
Proof.
  move E  : (Univ i) => T h.
  move : B B' M M' N N' i E.
  elim : Γ A A' T / h.
  - move => Γ M N A h B B' M0 M' N0 N' i ? h0 h1 h2. subst.
    apply WRs_Trans with (N := App B M0 N0).
    eapply WR_App with (i := i); eauto 3 with wt.
    have : Γ ⊢ M0 ▻+ M' ∈ Pi N B.
    apply : WRs_Conv; eauto.
    apply wrs_Equiv with (i := i).
    apply WRs_One.
    apply WR_Prod; eauto with wt.
    move /WRs_Ctx_step in h0. move/(_ _ _ ltac:(by eauto with wt)) in h0.
    move /WRs_Conv in h2.
    move /(_ N ltac:(by eauto with wt)) in h2.
    move /wr_rh_refl in h.
    move {h1}  => h1 {M}.
    move E : (N :: Γ)  h0 M0 M' N0 N' h1 h2 => Δ h0.
    move : E.
    move E : (Univ i) h0  => T h0.
    move : E.
    elim : Δ B B' T / h0.
    + move => ? P P' A h0 ? ? M0 M' Q Q' h2 h3. subst.
      apply (WRs_Trans _ _ (App P' M0 Q)).
      apply : WR_App; eauto with wt.
      apply (WRs_Conv _ _ _ P'[Q..]); cycle 1.
      apply WE_Exp with (i := i).
      change (Univ i) with (Univ i)[Q..].
      eauto using WR_cong with wt.
      have : Γ ⊢ Pi N P ≡ Pi N P' by eauto with wt.
      move  /WRs_Conv : h2. move/[apply] => h2.
      move /wr_rh_refl in h0.
      move {P}.
      move : Q Q' h3.
      move E : (Pi N P') h2  => T h2.
      move : h h0 E.
      elim : Γ M0 M' T / h2.
      * move => Γ M M' A hM hN hP' ? Q Q' hQ. subst.
        apply WRs_Trans with (N := App P' M' Q); first by eauto with wt.
        move /wr_rh_refl in hM. move{M}.
        move : hN hP' hM.
        elim : Γ Q Q' N  / hQ; first by eauto with wt.
        move => Γ M0 M1 M2 A hM0 hM1 ih hA hP' hM'.
        apply WRs_Trans with (N := App P' M' M1); first by eauto with wt.
        move /(_ hA hP' hM') : ih.
        move /WRs_Conv. apply.
        apply WE_Exp with (i := i).
        eauto using WR_cong_univ with wt.
      * hauto lq:on db:wt.
    + move => Γ0 M0 N0 P A hM0 hN0 ih ? ? M1 M' N1 N' h0 h1. subst.
      specialize ih with (1 := eq_refl) (2 := eq_refl).
      apply WRs_Trans with (N := App N0 M1 N1).
      eapply WR_App with (i := i); eauto with wt.
      apply : WRs_Conv.
      apply ih; eauto with wt.
      eauto using WRs_Conv with wt.
      eauto using WR_cong_univ with wt.
  - move => Γ M N P A hM hN ih B B' M0 M' N0 N' i ? hB hM0 hN0. subst.
    have h0 : Γ ⊢ M ≡ N by eauto with wt.
    have h1 : ⊢ N :: Γ by qauto l:on use:rh_refl_mutual db:wt.
    specialize ih with (1 := eq_refl).
    apply WRs_Trans with (N := App B M0 N0).
    eapply WR_App with (i := i); sfirstorder use:lh_refl_mutual.
    apply ih.
    move : WRs_Ctx_conv hB (h0) (h1); repeat move/[apply]. exact.
    apply : WRs_Conv; eauto.
    apply : (wrs_Equiv _ _ _ i).
    apply WRs_One.
    apply WR_Prod=>//. sfirstorder use:lh_refl_mutual.
    apply : WRs_Conv; eauto.
Qed.

Lemma Prod_multi_inv Γ A B N T :
  Γ ⊢ Pi A B ▻+ N ∈ T ->
  exists A' B' i,
    N = Pi A' B' /\ Γ ⊢ A ▻+ A' ∈ Univ i /\ A :: Γ ⊢ B ▻+ B' ∈ Univ i  /\ Γ ⊢ T ≡ Univ i.
Proof.
  move E : (Pi A B) => U h.
  move : A B E. elim : Γ U N T / h.
  - move => > h *. subst.
    move /Prod_inv in h.
    hauto lq:on db:wt.
  - move => Γ M N PA A hM hN ih A0 B ?. subst.
    move /Prod_inv : hM.
    move =>[A'][B'][i][?][h0][h1]h2. subst.
    specialize ih with (1 := eq_refl).
    move : ih => [A'0][B'0][i0][?][h3][h4]h5. subst.
    exists A'0, B'0, i. repeat split =>//.
    apply : WRs_Trans; first by eassumption.
    move /wr_rh_refl : h0.
    move :h3. apply exchange_multi_step.
    move /Ctx_step /(_ h0) in h1.
    apply : WRs_Ctx_conv; eauto with wt.
    apply : WRs_Trans; first by eassumption.
    move /wr_rh_refl : h1.
    move : h4. apply exchange_multi_step.
Qed.

(* Lemma Lam_multi_inv Γ A M N T *)
(*   (h : Γ ⊢ Lam A M ▻+ N ∈ T) : *)
(*   exists A' M' B i, *)
(*     (* N = Lam A' M' /\ *) *)
(*     Γ ⊢ A ▻+ A' ∈ Univ i /\ *)
(*     A::Γ ⊢ B ▻ B ∈ Univ i /\ *)
(*     A::Γ ⊢ M ▻+ M' ∈ B /\ *)
(*     Γ ⊢ T ≡ Pi A B. *)
(* Proof. *)
(*   move E : (Lam A M) h => A0 h. *)
(*   move : A M E. *)
(*   elim : Γ A0 N T / h. *)
(*   - move => > h *. subst. *)
(*     move /Lam_inv in h. *)
(*     hauto lq:on db:wt. *)
(*   - move => Γ M N P A h0 h1 ih A0 M0 ?. subst. *)
(*     move /Lam_inv : h0 => [A'][M'][B][i][h2][h3][h4]h9. subst. *)
(*     specialize ih with (1 := eq_refl). *)
(*     move : ih=>[A'0][M'0][B'][i0][?][h5][h6][h7]h8. subst. *)
(*     exists A'0, M'0, B, i. repeat split =>//. *)
(*     apply : WRs_Trans; eauto 2. *)
(*     hauto lq:on rew:off use:exchange_multi_step db:wt. *)
(*     apply : WRs_Ctx_conv; eauto 2 with wt. *)
(*     move /Ctx_step /(_ h2) in h4. *)
(*     hauto lq:on rew:off use:exchange_multi_step db:wt. *)
(* Qed. *)

Lemma Univ_multi_inv Γ i N T (h : Γ ⊢ Univ i ▻+ N ∈ T) :
  N = Univ i /\ Γ ⊢ T ≡ Univ (S i).
Proof.
  move E : (Univ i) h => U h.
  move : E.
  elim : Γ U N T / h.
  - move => > h *. subst. move/Univ_inv in h. hauto lq:on db:wt.
  - move => Γ M N P A + h1 ih ?. subst.
    move /Univ_inv => [?]h2. subst.
    sfirstorder.
Qed.

Lemma regularity Γ M N A
  (h : Γ ⊢ M ▻ N ∈ A) :
  exists i, Γ ⊢ A ▻ A ∈ Univ i.
Proof.
  elim : Γ M N A / h; eauto with wt.
  - sfirstorder use:lookup_wf.
  - move => Γ A A' i B B' M M' N N' hA
             [i0 ihA] hB [i1 ihB] hM [i2 ihM] hN [i3 ihN].
    move /Prod_inv : ihM.
    move => [A'0][B'0][i4][?][?]?.
    exists i4. change (Univ i4) with (Univ i4)[N..].
    qauto l:on use:WR_cong, lh_refl_mutual, rh_refl_mutual db:wt.
  - move => Γ A i B B' M M' N N' hA [i0 ihA]
             hB [i2 ihB] hM [i3 ihM] hN [i4 ihN].
    exists i3.
    change (Univ i3) with (Univ i3)[N..].
    qauto l:on use:WR_cong, lh_refl_mutual, rh_refl_mutual db:wt.
Qed.

Lemma WRs_Trans0 Γ a b c A : Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ b ▻+ c ∈ A -> Γ ⊢ a ▻+ c ∈ A.
Proof.
  move => h. move : c.
  elim : Γ a b A / h; eauto with wt.
Qed.

Lemma WRs_TransR Γ a b c A : Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ b ▻ c ∈ A -> Γ ⊢ a ▻+ c ∈ A.
Proof.
  eauto using WRs_Trans0 with wt.
Qed.

Notation "Γ ⊢ a ∈  A" := (Γ ⊢ a ▻ a ∈ A) (at level 70, no associativity).


Reserved Notation "Γ ⊢ a ▻β b ∈  A" (at level 70, no associativity).
Inductive WtBRed : context -> tm -> tm -> tm -> Prop :=
| WB_Var Γ n A :
  ⊢ Γ ->
  lookup n Γ A ->
  (* ------------- *)
  Γ ⊢ var_tm n ▻β var_tm n ∈ A

| WB_Univ Γ i :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ Univ i ▻β Univ i ∈ Univ (S i)

| WB_Prod Γ i A A' B B' :
  Γ ⊢ A ▻β A' ∈ Univ i ->
  A :: Γ ⊢ B ▻β B' ∈ Univ i ->
  (* ------------------- *)
  Γ ⊢ Pi A B ▻β Pi A' B' ∈ Univ i

| WB_Lam Γ A A' i B M M' :
  Γ ⊢ A ▻β A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  A :: Γ ⊢ M ▻β M' ∈ B ->
  (* ------------------ *)
  Γ ⊢ Lam A M ▻β Lam A' M' ∈ Pi A B

| WB_App Γ A i B B' M M' N N' :
  Γ ⊢ A ▻ A ∈ Univ i ->
  A :: Γ ⊢ B ▻β B' ∈ Univ i ->
  Γ ⊢ M ▻β M' ∈ Pi A B ->
  Γ ⊢ N ▻β N' ∈ A ->
  (* ------------------------ *)
  Γ ⊢ App B M N ▻β App B' M' N' ∈ B[N..]

| WB_Beta Γ A i B M M' N N' :
  Γ ⊢ A ▻ A ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  A :: Γ ⊢ M ▻β M' ∈ B ->
  Γ ⊢ N ▻β N' ∈ A ->
  (*----------------------  *)
  Γ ⊢ App B (Lam A M) N ▻β M'[N'..] ∈ B[N..]

| WB_Conv Γ M N A B :
  Γ ⊢ M ▻β N ∈ A ->
  Γ ⊢ A ≡ B ->
  (* ----------------- *)
  Γ ⊢ M ▻β N ∈ B
where
"Γ ⊢ a ▻β b ∈ A" := (WtBRed Γ a b A).

Reserved Notation "Γ ⊢ a ▻η b ∈  A" (at level 70, no associativity).
Inductive WtExp : context -> tm -> tm -> tm -> Prop :=
| WE_Var Γ n A :
  ⊢ Γ ->
  lookup n Γ A ->
  (* ------------- *)
  Γ ⊢ var_tm n ▻η var_tm n ∈ A

| WE_Univ Γ i :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ Univ i ▻η Univ i ∈ Univ (S i)

| WE_Prod Γ i A A' B B' :
  Γ ⊢ A ▻η A' ∈ Univ i ->
  A :: Γ ⊢ B ▻η B' ∈ Univ i ->
  (* ------------------- *)
  Γ ⊢ Pi A B ▻η Pi A' B' ∈ Univ i

| WE_Lam Γ A A' i B M M' :
  Γ ⊢ A ▻η A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  A :: Γ ⊢ M ▻η M' ∈ B ->
  (* ------------------ *)
  Γ ⊢ Lam A M ▻η Lam A' M' ∈ Pi A B

| WE_App Γ A i B B' M M' N N' :
  Γ ⊢ A ▻ A ∈ Univ i ->
  A :: Γ ⊢ B ▻η B' ∈ Univ i ->
  Γ ⊢ M ▻η M' ∈ Pi A B ->
  Γ ⊢ N ▻η N' ∈ A ->
  (* ------------------------ *)
  Γ ⊢ App B M N ▻η App B' M' N' ∈ B[N..]

| WE_Eta Γ a b A A' i B B'  :
  Γ ⊢ A ▻η A' ∈ Univ i ->
  A :: Γ ⊢ B ▻η B' ∈ Univ i ->
  Γ ⊢ a ▻η b ∈  Pi A B ->
  Γ ⊢ a ▻η Lam A' (App (B'⟨upRen_tm_tm shift⟩) (b⟨shift⟩) (var_tm var_zero)) ∈ Pi A B

| WE_Conv Γ M N A B :
  Γ ⊢ M ▻η N ∈ A ->
  Γ ⊢ A ≡ B ->
  (* ----------------- *)
  Γ ⊢ M ▻η N ∈ B
where
"Γ ⊢ a ▻η b ∈ A" := (WtExp Γ a b A).

Lemma WE_Eta' Γ a b A A' i B B' u  :
  u = Lam A' (App B'⟨upRen_tm_tm shift⟩ b⟨shift⟩ (var_tm var_zero)) ->
  Γ ⊢ A ▻η A' ∈ Univ i ->
  A :: Γ ⊢ B ▻η B' ∈ Univ i ->
  Γ ⊢ a ▻η b ∈  Pi A B ->
  Γ ⊢ a ▻η u ∈ Pi A B.
Proof. move => ->. apply WE_Eta. Qed.

Lemma WtBRed_embed Γ a b A : Γ ⊢ a ▻β b ∈ A -> Γ ⊢ a ▻ b ∈ A.
Proof.
  move => h. elim : Γ a b A / h; eauto using WR_Conv with wt.
Qed.

Lemma WtExp_embed Γ a b A : Γ ⊢ a ▻η b ∈ A -> Γ ⊢ a ▻ b ∈ A.
Proof.
  move => h. elim : Γ a b A / h; eauto using WR_Conv with wt.
Qed.

Inductive URed Γ a b A : Prop :=
| U_β : Γ ⊢ a ▻β b ∈ A -> URed Γ a b A
| U_η : Γ ⊢ a ▻η b ∈ A -> URed Γ a b A.

Inductive UReds Γ : tm -> tm -> tm ->  Prop :=
| U_Refl a A : Γ ⊢ a ▻ a ∈ A -> UReds Γ a a A
| U_Step a b c A :
  URed Γ a b A ->
  UReds Γ b c A ->
  UReds Γ a c A.

Lemma UReds_transitive Γ a b c A  :
  UReds Γ a b A ->
  UReds Γ b c A ->
  UReds Γ a c A.
Proof.
  move => h. move : c.
  elim : a b A / h => //.
  hauto lq:on ctrs:UReds.
Qed.

Lemma U_Once Γ a b A :
  URed Γ a b A ->
  UReds Γ a b A.
Proof.
  move => h.
  apply : U_Step; eauto.
  apply U_Refl.
  elim : h.
  - move /WtBRed_embed. sfirstorder use:rh_refl_mutual.
  - move /WtExp_embed. sfirstorder use:rh_refl_mutual.
Qed.

Lemma U_Onceβ Γ a b A :
  WtBRed Γ a b A ->
  UReds Γ a b A.
Proof. sfirstorder use:U_Once, U_β. Qed.

Lemma U_Onceη Γ a b A :
  WtExp Γ a b A ->
  UReds Γ a b A.
Proof. sfirstorder use:U_Once, U_η. Qed.

#[export]Hint Constructors WtBRed : bred.
#[export]Hint Constructors WtExp : eexp.

Definition β_morphing_ok ρ Γ Δ := forall n A, lookup n Γ A -> Δ ⊢ ρ n ▻β ρ n ∈ A[ρ].

Lemma β_morphing_ok_embed ρ Γ Δ :
  β_morphing_ok ρ Γ Δ -> lookup_good_morphing ρ Γ Δ.
Proof. sfirstorder use:WtBRed_embed. Qed.


Lemma WB_App' Γ A i B B' M M' N N' U :
  U = B[N..] ->
  Γ ⊢ A ▻ A ∈ Univ i ->
  A :: Γ ⊢ B ▻β B' ∈ Univ i ->
  Γ ⊢ M ▻β M' ∈ Pi A B ->
  Γ ⊢ N ▻β N' ∈ A ->
  (* ------------------------ *)
  Γ ⊢ App B M N ▻β App B' M' N' ∈ U.
Proof. move => ->. apply WB_App. Qed.

Lemma WE_App' Γ A i B B' M M' N N' U :
  U = B[N..] ->
  Γ ⊢ A ▻ A ∈ Univ i ->
  A :: Γ ⊢ B ▻η B' ∈ Univ i ->
  Γ ⊢ M ▻η M' ∈ Pi A B ->
  Γ ⊢ N ▻η N' ∈ A ->
  (* ------------------------ *)
  Γ ⊢ App B M N ▻η App B' M' N' ∈ U.
Proof. move => ->. apply WE_App. Qed.

Lemma WB_Beta' Γ A i B M M' N N' U0 U1 :
  U0 = M'[N'..] ->
  U1 = B[N..] ->
  Γ ⊢ A ▻ A ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  A :: Γ ⊢ M ▻β M' ∈ B ->
  Γ ⊢ N ▻β N' ∈ A ->
  (*----------------------  *)
  Γ ⊢ App B (Lam A M) N ▻β U0 ∈ U1.
Proof. move => -> ->. apply WB_Beta. Qed.

Lemma wt_β_renaming :
  (forall Γ a b A, Γ ⊢ a ▻β b ∈ A -> forall ξ Δ,
        lookup_good_renaming ξ Γ Δ -> Wf Δ -> Δ ⊢ a⟨ξ⟩ ▻β b⟨ξ⟩ ∈ A⟨ξ⟩ ).
Proof.
  move => Γ a b A h.
  elim : Γ a b A / h; eauto with bred.
  - move => Γ n A hΓ hn ξ Δ hξ hΔ.
    constructor; eauto.
  - move => *. constructor; eauto.
  - move => Γ i A A' B B' hA ihA hB ihB ξ Δ hξ hΔ /=.
    apply WB_Prod; eauto.
    apply ihB. hauto l:on use:good_renaming_up.
    econstructor; eauto.
    apply WtBRed_embed. apply ihA; eauto.
  - move => Γ A A' i B M M' hA ihA hB hM ihM ξ Δ hξ hΔ [:tr0] /=.
    apply : WB_Lam; eauto.
    eapply wt_renaming_univ; eauto.
    hauto l:on use:good_renaming_up.
    abstract : tr0.
    econstructor; eauto. sfirstorder use:WtBRed_embed.
    apply ihM. hauto l:on use:good_renaming_up.
    assumption.
  - move => Γ A i B B' M M' N N' hA hB ihB hM ihM hN ihN ξ Δ hξ hΔ [:tr0]/=.
    apply : WB_App'; eauto. by asimpl.
    rewrite -/ren_tm. abstract : tr0.
    sfirstorder use:wt_renaming_univ.
    rewrite -/ren_tm.
    apply ihB. hauto l:on use:good_renaming_up.
    econstructor; eauto.
    apply tr0.
  - move => Γ A i B M M' N N' ha hB hM ihM hN ihN ξ Δ hξ hΔ [:tr0].
    apply : WB_Beta'; cycle 1; eauto; rewrite -/ren_tm.
    by asimpl.
    abstract : tr0.
    sfirstorder use:wt_renaming_univ.
    hauto lq:on  use:good_renaming_up, wt_renaming_univ db:wt.
    hauto q:on use:good_renaming_up db:wt.
    by asimpl.
  - hauto lq:on use:equiv_renaming db:bred.
Qed.

Lemma βmorphing_up ρ k Γ Δ A B
  (h : β_morphing_ok ρ Γ Δ) :
  Δ ⊢ A[ρ] ▻β B ∈ Univ k ->
  β_morphing_ok (up_tm_tm ρ) (A :: Γ) (A [ρ] :: Δ).
Proof.
  rewrite /lookup_good_morphing => h1.
  have hΔ : ⊢ (A [ρ] :: Δ) by
    hauto lq:on use:β_morphing_ok_embed, WtBRed_embed db:wt.
  inversion 1=>*; subst.
  - apply WB_Var => //.
    asimpl. apply : here'. by asimpl.
  - asimpl. rewrite !subst_ren_factor.
    eapply wt_β_renaming. hauto l:on unfold:lookup_good_morphing.
    apply lookup_good_renaming_shift.
    eauto with wt.
Qed.


Lemma β_lh_refl Γ a b A :
  Γ ⊢ a ▻ b ∈ A ->
  Γ ⊢ a ▻β a ∈ A.
Proof.
  move => h. elim : Γ a b A / h; eauto with bred.
  - qauto l:on use:lh_refl_mutual db:bred.
  - move => Γ A i B B' M M' N N' ha ihA hB ihB' hM ihM' hN ihN'.
    apply : WB_App; cycle 1. eauto. apply : WB_Lam; eauto. sfirstorder use:lh_refl_mutual.
    sfirstorder use:lh_refl_mutual.
    eauto.
  - hauto lq:on use:WB_Conv, WE_Red.
  - hauto lq:on use:WB_Conv, WE_Exp.
Qed.

Lemma η_lh_refl Γ a b A :
  Γ ⊢ a ▻ b ∈ A ->
  Γ ⊢ a ▻η a ∈ A.
Proof.
  move => h. elim : Γ a b A / h; eauto with eexp.
  - qauto l:on use:lh_refl_mutual db:eexp.
  - hauto lq:on use:lh_refl_mutual db:eexp.
  - hauto lq:on use:WE_Conv, WE_Red.
  - hauto lq:on use:WE_Conv, WE_Exp.
Qed.

Lemma morphing_ok_β_embed ρ Γ Δ :
  lookup_good_morphing ρ Γ Δ -> β_morphing_ok ρ Γ Δ.
Proof.
  rewrite /lookup_good_morphing /β_morphing_ok.
  sfirstorder use:β_lh_refl.
Qed.

Lemma wt_β_morphing :
  (forall Γ a b A, Γ ⊢ a ▻β b ∈ A -> forall ρ Δ,
        β_morphing_ok ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻β b[ρ] ∈ A[ρ] ).
Proof.
  move => Γ a b A ha.
  elim : Γ a b A / ha => /=; eauto with bred.
  - move => Γ i A A' B B' hA ihA hB ihB ρ Δ hρ hΔ.
    constructor; eauto. apply ihB.
    qauto l:on use:βmorphing_up.
    econstructor; eauto.
    apply WtBRed_embed. apply ihA; eauto.
  - move => Γ A A' i B M M' hA ihA hB hM ihM ρ Δ hρ hΔ.
    have hΔ' : ⊢ A [ρ] :: Δ.
    econstructor; eauto. hauto lq:on use:β_morphing_ok_embed, WtBRed_embed db:wt.
    apply : WB_Lam; eauto.
    sauto lq:on use:good_morphing_up, β_morphing_ok_embed, wt_morphing_univ.
    sauto lq:on use:βmorphing_up.
  - move => Γ A i B B' M M' N N' hA hB ihB hM ihM hN ihN ρ Δ hρ hΔ [:tr0].
    apply : WB_App'; eauto. by asimpl.
    apply : wt_morphing_univ; eauto.
    hauto lq:on use:β_morphing_ok_embed.
    apply ihB. apply : βmorphing_up=>//.
    apply : β_lh_refl; eauto.
    abstract : tr0.
    hauto lq:on use:β_morphing_ok_embed, wt_morphing_univ.
    econstructor; eauto.
    apply tr0.
  - move => Γ A i B M M' N N' hA hB hM ihM hN ihN ρ Δ hρ hΔ [:tr0] [:tr1].
    apply : WB_Beta'; eauto; cycle 2.
    abstract : tr0.
    have /β_lh_refl hA' := hA.
    hauto lq:on use:β_morphing_ok_embed, wt_morphing_univ.
    apply : wt_morphing_univ; eauto.
    apply : good_morphing_up; eauto. by apply β_morphing_ok_embed.
    apply tr0.
    abstract : tr1.
    econstructor. apply tr0.
    apply ihM.
    apply : βmorphing_up; eauto.
    apply /β_lh_refl /tr0. apply /tr1.
    by asimpl.
    by asimpl.
  - move => Γ M N A B hM ihM hC ρ Δ hρ hΔ.
    apply : WB_Conv; eauto.
    sfirstorder use:equiv_morphing, β_morphing_ok_embed.
Qed.

Lemma wt_η_morphing :
  (forall Γ a b A, Γ ⊢ a ▻η b ∈ A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻η b[ρ] ∈ A[ρ] ).
Proof.
  move => Γ a b A ha.
  elim : Γ a b A / ha.
  - move => Γ n A hΓ hn. sfirstorder use:η_lh_refl.
  - hauto q:on use:good_morphing_up, wt_morphing_univ db:eexp.
  - hauto q:on use:good_morphing_up, wt_morphing_univ, WtExp_embed db:eexp, wt.
  - hauto q:on use:good_morphing_up, wt_morphing_univ, WtExp_embed db:eexp, wt.
  - move => *.
    apply : WE_App'; eauto using wt_morphing_univ. rewrite -/subst_tm.
    by asimpl. rewrite -/subst_tm.
    qauto l:on use:good_morphing_up, WtExp_embed, wt_morphing_univ db:wt, eexp.
  - move => Γ a b A A' i B B' hA ihA hB ihB ha iha ρ Δ hρ hΔ /=.
    apply : WE_Eta'; eauto using good_morphing_up with wt; cycle 1.
    apply ihB. hauto lq:on use:good_morphing_up, wt_morphing_univ, WtExp_embed db:wt, eexp.
    hauto lq:on use:good_morphing_up, wt_morphing_univ, WtExp_embed db:wt, eexp.
    by asimpl.
  - hauto lq:on use:equiv_morphing, WE_Conv.
Qed.

Lemma renaming_to_morphing:
  forall (Γ : context) (ξ : nat -> nat) (Δ : context),
    ⊢ Δ ->
    lookup_good_renaming ξ Γ Δ -> lookup_good_morphing (funcomp var_tm ξ) Γ Δ.
Proof.
  intros Γ ξ Δ hΔ.
  rewrite /lookup_good_renaming /lookup_good_morphing.
  move => hξ i A /hξ hl.
  constructor => //.
  by renamify.
Qed.

Lemma wt_η_renaming :
  (forall Γ a b A, Γ ⊢ a ▻η b ∈ A -> forall ξ Δ,
        lookup_good_renaming ξ Γ Δ -> Wf Δ -> Δ ⊢ a⟨ξ⟩ ▻η b⟨ξ⟩ ∈ A⟨ξ⟩).
Proof.
  move => Γ a b A ha ξ Δ hξ hΓ. substify.
  apply : wt_η_morphing; eauto using renaming_to_morphing.
Qed.

Lemma βη_lh_refl Γ a b A :
  Γ ⊢ a ▻ b ∈ A ->
  URed Γ a a A.
Proof. sfirstorder inv:URed use:β_lh_refl, η_lh_refl. Qed.


Lemma equiv_regularity0 Γ A B :
  Γ ⊢ A ≡ B ->
  exists i, Γ ⊢ A ∈ Univ i /\ Γ ⊢ B ∈ Univ i.
Proof.
  move => h. elim : A B /h.
  - hauto l:on use:lh_refl_mutual, rh_refl_mutual.
  - hauto l:on use:lh_refl_mutual, rh_refl_mutual.
  - move => A B C h0 [i [h1 h2]] h5 [j [h3 h4]].
    have ? : j = i by sfirstorder use:unique_sorts_mutual. subst.
    eauto.
Qed.

Lemma βCtx_conv A B Γ M N C (h : A :: Γ ⊢ M ▻β N ∈ C) (h1 : Γ ⊢ A ≡ B) :
  B :: Γ ⊢ M ▻β N ∈ C.
Proof.
  move /wt_β_morphing /(_ var_tm) : h. asimpl. apply=>//.
  apply /morphing_ok_β_embed /lookup_good_id; eauto.
  hauto lq:on use:equiv_regularity0 db:wt.
  move : h1. apply Equiv_sym.
  hauto lq:on use:equiv_regularity0 db:wt.
Qed.

Lemma ηCtx_conv A B Γ M N C (h : A :: Γ ⊢ M ▻η N ∈ C) (h1 : Γ ⊢ A ≡ B) :
  B :: Γ ⊢ M ▻η N ∈ C.
Proof.
  move /wt_η_morphing /(_ var_tm) : h. asimpl. apply=>//.
  apply /lookup_good_id; eauto.
  hauto lq:on use:equiv_regularity0 db:wt.
  move : h1. apply Equiv_sym.
  hauto lq:on use:equiv_regularity0 db:wt.
Qed.

Lemma βCtx_step A B i Γ M N C (h : A :: Γ ⊢ M ▻β N ∈ C) (h1 : Γ ⊢ A ▻ B ∈ Univ i) :
  B :: Γ ⊢ M ▻β N ∈ C.
Proof.
  apply : βCtx_conv; eauto with wt bred.
Qed.

Lemma ηCtx_step A B i Γ M N C (h : A :: Γ ⊢ M ▻η N ∈ C) (h1 : Γ ⊢ A ▻ B ∈ Univ i) :
  B :: Γ ⊢ M ▻η N ∈ C.
Proof.
  apply : ηCtx_conv; eauto with wt bred.
Qed.

Lemma Prod_congU0 Γ A A' B B' i :
  URed Γ A A' (Univ i) ->
  URed (A :: Γ) B B' (Univ i) ->
  UReds Γ (Pi A B) (Pi A' B') (Univ i).
Proof.
  move => [h0 | h0] [h1 | h1].
  - hauto lq:on use:U_Onceβ ctrs:WtBRed.
  - apply : U_Step.
    apply U_β. constructor; eauto.
    hauto lq:on use:β_lh_refl, WtExp_embed.
    apply U_Once.
    apply U_η.
    constructor. hauto lq:on use:WtBRed_embed, η_lh_refl, rh_refl_mutual.
    hauto lq:on use:ηCtx_step, WtBRed_embed.
  - apply : U_Step.
    apply U_η. constructor; eauto.
    hauto lq:on use:η_lh_refl, WtBRed_embed.
    apply U_Once.
    apply U_β.
    constructor. hauto lq:on use:WtExp_embed, β_lh_refl, rh_refl_mutual.
    hauto lq:on use:βCtx_step, WtExp_embed.
  - hauto lq:on use:U_Onceη ctrs:WtExp.
Qed.

Lemma wt_βη_morphing :
  (forall Γ a b A, URed Γ a b A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> URed Δ (a[ρ]) (b[ρ]) A[ρ] ).
Proof.
  move => Γ a b A [h|h].
  - move => ρ Δ hρ hΔ. apply U_β.
    sfirstorder use:morphing_ok_β_embed, wt_β_morphing.
  - move => ρ Δ hρ hΔ. apply U_η.
    sfirstorder use:wt_η_morphing.
Qed.

Lemma βηCtx_conv A B Γ M N C (h : URed (A :: Γ) M N C) (h1 : Γ ⊢ A ≡ B)
  (h2 : ⊢ B :: Γ) :
  URed (B :: Γ) M N C.
Proof.
  move /wt_βη_morphing /(_ var_tm) : h. asimpl. apply=>//.
  apply /lookup_good_id; eauto.
  move : h1. apply Equiv_sym.
Qed.

Lemma URed_embed Γ a b A :
  URed Γ a b A ->
  Γ ⊢ a ▻ b ∈ A.
Proof. sfirstorder inv:URed use:WtBRed_embed, WtExp_embed. Qed.

Lemma βηCtx_step A B i Γ M N C (h : URed (A :: Γ) M N C) (h1 : URed Γ A B (Univ i)) :
  URed (B :: Γ) M N C.
Proof.
  apply : βηCtx_conv; eauto using URed_embed with wt.
Qed.

Lemma Prod_congU1 Γ A A' B  i :
  UReds Γ A A' (Univ i) ->
  A :: Γ ⊢ B ∈ Univ i ->
  UReds Γ (Pi A B) (Pi A' B) (Univ i).
Proof.
  move E : (Univ i) => u hu.
  move : i E.
  elim : A A' u / hu.
  - move => A ? ha + + h1.
    move => i ?. subst.
    apply U_Refl.
    eauto with wt.
  - move => A0 A1 A2 T h0 h1 ih1 i ?. subst.
    spec_refl.
    move => h2.
    apply : UReds_transitive; eauto.
    apply Prod_congU0 => //; eauto using βη_lh_refl.
    apply ih1.
    apply : Ctx_step; eauto using URed_embed.
Qed.

Lemma Prod_congU2 Γ A B B' i :
  Γ ⊢ A ∈ Univ i ->
  UReds (A :: Γ) B B' (Univ i) ->
  UReds Γ (Pi A B) (Pi A B') (Univ i).
Proof.
  move => hA.
  move E : (Univ i) => U hu.
  move : E.
  elim : B B' U  /hu.
  - move => B ? hB ?. subst.
    apply U_Once.
    apply : βη_lh_refl; eauto with wt.
  - move => B B' B'' ? h0 h1 ih ?. subst. spec_refl.
    apply : UReds_transitive; eauto.
    apply Prod_congU0;
    eauto using βη_lh_refl.
Qed.

Lemma UReds_embed Γ a b A :
  UReds Γ a b A ->
  Γ ⊢ a ▻+ b ∈ A.
Proof.
  move => h. elim : a b A / h=>//; eauto with wt.
  hauto lq:on use:URed_embed db:wt.
Qed.

Lemma UReds_wt Γ a b A :
  UReds Γ a b A ->
  Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A.
Proof.
  hauto lq:on use:UReds_embed, lh_refl_mutual, rh_refl_mutual.
Qed.

Lemma Prod_congU Γ A A' B B' i :
  UReds Γ A A' (Univ i) ->
  UReds (A :: Γ) B B' (Univ i) ->
  UReds Γ (Pi A B) (Pi A' B') (Univ i).
Proof.
  move => hA hB.
  apply : UReds_transitive.
  apply Prod_congU2; hauto lq:on use:UReds_wt.
  apply Prod_congU1; eauto. hauto l:on use:UReds_wt.
Qed.

Lemma WtRed_UReds Γ a b A :
  Γ ⊢ a ▻ b ∈ A ->
  UReds Γ a b A.
Proof.
  move => h.
  elim : Γ a b A / h.
  - move => Γ n A hΓ hn. by apply /U_Once /U_β /WB_Var.
  - move => Γ i hΓ. by apply /U_Once /U_β /WB_Univ.
  - eauto using Prod_congU.
  - move => Γ A A' i B M M'.
    admit.
Admitted.

Module BInv.
  Lemma Var_inv Γ n N T (h : Γ ⊢ var_tm n ▻β N ∈ T) :
    exists A, N = var_tm n /\ lookup n Γ A /\ Γ ⊢ A ≡ T .
  Proof.
    move E : (var_tm n) h => M h.
    move : n E.
    elim : Γ M N T / h=>//.
    - hauto lq:on use:lookup_wf db:wt.
    - move => Γ M N A B hM ihM hE n ?. subst.
      spec_refl. hauto lq:on db:wt.
  Qed.

  Lemma Univ_inv Γ i N T (h : Γ ⊢ Univ i ▻β N ∈ T) :
    N = Univ i /\ Γ ⊢ Univ (S i) ≡ T.
  Proof.
    move E : (Univ i) h => M h.
    move : i E.
    elim : Γ M N T / h=>//; try hauto lq:on rew:off db:wt.
  Qed.

  Lemma Prod_inv Γ A B N T (h : Γ ⊢ Pi A B ▻β N ∈ T) :
    exists A' B' i, N = Pi A' B' /\ Γ ⊢ A ▻β A' ∈ Univ i /\ A::Γ ⊢ B ▻β B' ∈ Univ i /\ Γ ⊢ Univ i ≡ T.
  Proof.
    move E : (Pi A B) h => M h.
    move : A B E.
    elim : Γ M N T / h=>//.
    - move => Γ i A A' B B' hA _ hB _ A0 B0 [*]. subst.
      exists A',B',i. repeat split => //=.
      hauto lq:on use:Wt_Wf_mutual, WtBRed_embed db:wt.
    - hauto lq:on db:wt.
  Qed.

  Lemma Lam_inv Γ A M N T (h : Γ ⊢ Lam A M ▻β N ∈ T) :
    exists A' M' B i,
      N = Lam A' M' /\
      Γ ⊢ A ▻β A' ∈ Univ i /\
        A::Γ ⊢ B ∈ Univ i /\
        A::Γ ⊢ M ▻β M' ∈ B /\
        Γ ⊢ Pi A B ≡ T.
  Proof.
    move E : (Lam A M) h => M0 h.
    move : A M E.
    elim : Γ M0 N T / h=>//.
    - hauto lq:on use:Wt_Wf_mutual, WtBRed_embed db:wt.
    - hauto lq:on rew:off db:wt.
  Qed.


  Lemma App_inv Γ P B Q N T (h : Γ ⊢ App B P Q ▻β N ∈ T) :
    exists A B' Q' i,
      Γ ⊢ A ▻ A ∈ Univ i /\ A::Γ ⊢ B ▻β B' ∈ Univ i /\ Γ ⊢ Q ▻β Q' ∈ A /\
        Γ ⊢ B[Q..] ≡ T /\
        (* App case *)
        ((exists P', Γ ⊢ P ▻β P' ∈ Pi A B /\ N = App B' P' Q') \/
           (* Beta case *)
           (exists R R', P = Lam A R /\ A::Γ ⊢ R ▻β R' ∈ B /\ N = R'[Q'..] )).
  Proof.
    move E : (App B P Q) h => M h.
    move : B P Q E.
    elim : Γ M N T / h=>//.
    - move => Γ A i B B' M M' N N' hA hB _ hM _ hN _ >[]*. subst.
      exists A, B', N', i.
      repeat split => //.
      (* Factor out the first bullet *)
      + apply : WE_Red.
        have : Γ ⊢ N ▻ N ∈ A by hauto lq:on use:WtBRed_embed, lh_refl_mutual.
        have : A :: Γ ⊢ B ▻ B' ∈ Univ i by hauto lq:on use:WtBRed_embed, lh_refl_mutual.
        move : WR_cong. repeat move/[apply].
        apply /(proj1 lh_refl_mutual).
      + sfirstorder.
    - move => Γ A i B M M' N N' hA hB hM _ hN _ > []*.
      subst. exists A, B, N', i.
      repeat split => //.
      (* Factor out the first bullet *)
      + sfirstorder use:β_lh_refl.
      + apply : equiv_morphing; eauto with wt.
        inversion 1; subst. simpl. asimpl. hauto lq:on use:lh_refl_mutual, WtBRed_embed.
        asimpl. constructor. sfirstorder use:Wt_Wf_mutual. done. sfirstorder use:Wt_Wf_mutual.
      + hauto lq:on.
    - hauto lq:on rew:off db:wt.
  Qed.

End BInv.

Lemma WB_Conv' Γ M N A B :
  Γ ⊢ M ▻β N ∈ A ->
  Γ ⊢ B ≡ A ->
  (* ----------------- *)
  Γ ⊢ M ▻β N ∈ B.
Proof. sfirstorder use:WB_Conv, Equiv_sym. Qed.

#[export]Hint Resolve βCtx_step : bred.


Lemma Ctx_conv_simpl A B Γ M N C (h : A :: Γ ⊢ M ▻ N ∈ C) (h1 : Γ ⊢ A ≡ B) :
  B :: Γ ⊢ M ▻ N ∈ C.
Proof.
  hauto lq:on use:Ctx_conv, equiv_regularity0 db:wt.
Qed.

Lemma equiv_to_equivhom Γ A B :
  Γ ⊢ A ≡ B ->
  exists i, Γ ⊢ A ≃ B ∈ i.
Proof. hauto lq:on use:equiv_cast', equiv_regularity0. Qed.

Lemma βunique Γ a b c A B : Γ ⊢ a ▻β b ∈ A -> Γ ⊢ a ▻β c ∈ B -> Γ ⊢ A ≡ B.
Proof.
  move /WtBRed_embed => h /WtBRed_embed h0.
  hauto lq:on use:lh_refl_mutual, unique_mutual.
Qed.

Lemma equiv_sort_unique Γ A B i j : Γ ⊢ A ≡ B -> Γ ⊢ A ∈ Univ i -> Γ ⊢ B ∈ Univ j -> i = j.
Proof.
  move /equiv_regularity0 => [k][h0]h1 h2 h3.
  qauto l:on use:unique_sorts_mutual.
Qed.

Lemma βexchange Γ a c A0 A1 :
  Γ ⊢ a ∈ A0 ->
  Γ ⊢ a ▻β c ∈ A1 ->
  Γ ⊢ a ▻β c ∈ A0.
Proof.
  move => h0 h1.
  have : Γ ⊢ A1 ≡ A0 by hauto lq:on use:WtBRed_embed, unique_mutual, lh_refl_mutual.
  sfirstorder use:WB_Conv.
Qed.

Lemma ηexchange Γ a c A0 A1 :
  Γ ⊢ a ∈ A0 ->
  Γ ⊢ a ▻η c ∈ A1 ->
  Γ ⊢ a ▻η c ∈ A0.
Proof.
  move => h0 h1.
  have : Γ ⊢ A1 ≡ A0 by hauto lq:on use:WtExp_embed, unique_mutual, lh_refl_mutual.
  sfirstorder use:WE_Conv.
Qed.

Lemma ηexchange'' Γ a c A0 A1 :
  Γ ⊢ a ∈ A0 ->
  Γ ⊢ a ▻η c ∈ A1 ->
  Γ ⊢ a ▻η c ∈ A0.
Proof.
  move => h0 h1.
  have : Γ ⊢ A1 ≡ A0 by hauto lq:on use:WtExp_embed, unique_mutual, lh_refl_mutual.
  sfirstorder use:WE_Conv.
Qed.

Lemma βexchange' Γ a b c A0 A1 :
  Γ ⊢ a ▻β b ∈ A0 ->
  Γ ⊢ a ▻β c ∈ A1 ->
  Γ ⊢ a ▻β c ∈ A0.
Proof.
  qauto l:on use:βexchange, WtBRed_embed, lh_refl_mutual, rh_refl_mutual.
Qed.

Lemma exchange' Γ a b A0 A1 :
  Γ ⊢ a  ∈ A0 ->
  Γ ⊢ a ▻ b ∈ A1 ->
  Γ ⊢ b ∈ A0.
Proof.
  qauto lq:on use:rh_refl_mutual, exchange.
Qed.

Definition βmorphing2_ok ρ0 ρ1 Γ Δ :=
  forall n A, lookup n Γ A -> Δ ⊢ ρ0 n ▻β ρ1 n ∈ A[ρ0].

Lemma βmorphing2_ren ρ0 ρ1 ξ Γ Δ Ξ :
  βmorphing2_ok ρ0 ρ1 Γ Δ ->
  lookup_good_renaming ξ Δ Ξ ->
  ⊢ Ξ ->
  βmorphing2_ok (funcomp (ren_tm ξ) ρ0) (funcomp (ren_tm ξ) ρ1) Γ Ξ.
Proof.
  rewrite /βmorphing2_ok. move => hρ hξ hΞ n A hn.
  rewrite /funcomp. asimpl.
  have -> : A [funcomp (ren_tm ξ) ρ0] = A[ρ0]⟨ξ⟩ by asimpl.
  apply : wt_β_renaming; eauto.
Qed.

Lemma morphing_ext ρ Γ Δ a A  :
  lookup_good_morphing ρ Γ Δ ->
  Δ ⊢ a ▻ a ∈ A[ρ] ->
  lookup_good_morphing (scons a ρ) (A :: Γ) Δ.
Proof.
  move => hρ ha.
  move => n A0.
  elim /lookup_inv=>//=_.
  + move =>  ? ? ? [*]. subst.
    asimpl. eauto using wr_lh_refl.
  + move => i A1 ? ? + ? [*]. subst.
    move => h. asimpl. by apply hρ.
Qed.

Lemma βmorphing2_ext ρ0 ρ1 Γ Δ a0 a1 A  :
  βmorphing2_ok ρ0 ρ1 Γ Δ ->
  Δ ⊢ a0 ▻β a1 ∈ A[ρ0] ->
  βmorphing2_ok (scons a0 ρ0) (scons a1 ρ1) (A :: Γ) Δ.
Proof.
  move => hρ ha.
  move => n A0.
  elim /lookup_inv=>//=_.
  + move =>  ? ? ? [*]. subst.
    by asimpl.
  + move => i A1 ? ? + ? [*]. subst.
    move => h. asimpl. by apply hρ.
Qed.

Lemma βmorphing2_ok_embed ρ0 ρ1 Γ Δ :
  βmorphing2_ok ρ0 ρ1 Γ Δ -> lookup_good_morphing2 ρ0 ρ1 Γ Δ.
Proof. sfirstorder use:WtBRed_embed. Qed.

Lemma βmorphing2_ok_embed' ρ0 ρ1 Γ Δ :
  βmorphing2_ok ρ0 ρ1 Γ Δ -> lookup_good_morphing ρ0 Γ Δ.
Proof.
  hauto lq:on use:βmorphing2_ok_embed, lookup_good_morphing2_lh_refl.
Qed.

Lemma βmorphing2_up ρ0 ρ1 Γ Δ A i :
  βmorphing2_ok ρ0 ρ1 Γ Δ ->
  Δ ⊢ A [ρ0] ∈ Univ i ->
  βmorphing2_ok (up_tm_tm ρ0) (up_tm_tm ρ1) (A :: Γ) (A[ρ0] :: Δ).
Proof.
  move => h0 h1. asimpl.
  apply βmorphing2_ext. apply : βmorphing2_ren; eauto with wt.
  apply lookup_good_renaming_shift.
  apply : WB_Var; eauto with wt. apply here'. by asimpl.
Qed.

Lemma βmorphing2 Γ a b A ρ0 ρ1 Δ : Γ ⊢ a ▻β b ∈ A ->
  βmorphing2_ok ρ0 ρ1 Γ Δ -> Wf Δ -> Δ ⊢ a[ρ0] ▻β b[ρ1] ∈ A[ρ0].
Proof.
  move => h. move : Δ ρ0 ρ1. elim : Γ a b A /h; try solve [simpl in *; eauto with bred].
  - hauto lq:on use:wr_lh_refl, WtBRed_embed, βmorphing2_up db:wt,bred.
  - move => Γ A A' i B M M' hA ihA hB hM ihM Δ ρ0 ρ1 hρ hΔ /=.
    have hρ0 : lookup_good_morphing ρ0 Γ Δ by hauto l:on use:βmorphing2_ok_embed'.
    have hA' : Δ ⊢ A[ρ0] ∈ Univ i by hauto lq:on use:wt_morphing_univ, WtBRed_embed, wr_lh_refl.
    have : βmorphing2_ok (up_tm_tm ρ0) (up_tm_tm ρ1) (A :: Γ) (A [ρ0] :: Δ)
      by apply : βmorphing2_up; eauto.
    move => /[dup] hρ' /βmorphing2_ok_embed' hρ''.
    apply : WB_Lam; eauto with bred.
    apply : wt_morphing_univ; eauto using βmorphing2_ok_embed with wt.
    eauto with wt.
  - move => Γ A i B B' M M' N N' hA hB ihB hM ihM hN ihN Δ ρ0 ρ1 hρ hΔ /=.
    have hρ0 : lookup_good_morphing ρ0 Γ Δ by eauto using βmorphing2_ok_embed'.
    have hA' : Δ ⊢ A[ρ0] ∈ Univ i by eauto using wt_morphing_univ.
    have hΔ' : ⊢ A[ρ0] :: Δ by eauto with wt.
    apply : WB_App'. by asimpl. apply hA'. apply ihB; by eauto using βmorphing2_up.
    by eauto using βmorphing2_up.
    by eauto using βmorphing2_up.
  - move => Γ A i B M M' N N' hA hB hM ihM hN ihN Δ ρ0 ρ1 hρ hΔ /=.
    have hρ0 : lookup_good_morphing ρ0 Γ Δ by eauto using βmorphing2_ok_embed'.
    have hA' : Δ ⊢ A[ρ0] ∈ Univ i by eauto using wt_morphing_univ.
    have hΔ' : ⊢ A[ρ0] :: Δ by eauto with wt.
    have hρ0' : lookup_good_morphing (up_tm_tm ρ0) (A :: Γ) (A [ρ0] :: Δ) by eauto using good_morphing_up.
    apply : WB_Beta'; eauto; cycle 1. by asimpl.
    by apply : wt_morphing_univ; eauto.
    by apply ihM; eauto using βmorphing2_up.
    by asimpl.
  - qauto l:on use:βmorphing2_ok_embed', equiv_morphing db:bred.
Qed.



Lemma βmorphing2_id Γ : ⊢ Γ -> βmorphing2_ok ids ids Γ Γ.
  move => hΓ. rewrite /βmorphing2_ok.
  asimpl. eauto with bred.
Qed.

Lemma β_diamond : forall Γ M N A P B, Γ ⊢ M ▻β N ∈ A -> Γ ⊢ M ▻β P ∈ B -> exists Q, Γ ⊢ N ▻β Q ∈ B /\ Γ ⊢ P ▻β Q ∈ A.
Proof.
  move => Γ M N A + + h.
  elim : Γ M N A / h.
  - move => Γ n A hΓ hn P B /[dup] h' /BInv.Var_inv.
    move => [A0 [h0 h1]].
    have ? : A0 = A by sfirstorder use:lookup_deter. subst.
    hauto lq:on db:bred.
  - qauto l:on ctrs:WtBRed use:BInv.Univ_inv.
  - move => Γ i A A' B B' hA ihA hB ihB P B0 /BInv.Prod_inv.
    move => [A'0][B'0][i0][?][h0][h1]h2. subst.
    move /ihA : (h0) => [A''][hA0]hA1.
    move /ihB : (h1) => [B''][hB0]hB1.
    exists (Pi A'' B'').
    split; eauto with bred.
    apply WB_Conv' with (A := Univ i0)=>//.
    by eauto using WtBRed_embed with bred.
    by eauto using Equiv_sym.
    by eauto using WtBRed_embed with bred.
  - move => Γ A A' i B M M' hA ihA hB hM ihM P B0 /BInv.Lam_inv.
    move => [A'0][M'0][B1][i0][?][h0][h1][h2]/Equiv_sym h3. subst.
    move /ihA : (h0) => [A''][hA0]hA1.
    move /ihM : (h2) => [M''][hM0]hM1.
    exists (Lam A'' M'').
    split; eauto with bred.
    + apply WB_Conv' with (A := Pi A' B1)=>//.
      apply : WB_Lam; eauto using WtBRed_embed with bred.
      apply : Ctx_step; eauto. sfirstorder use:WtBRed_embed.
      apply : WE_Trans; eauto.
      apply : WE_Red.
      move /WtBRed_embed in hA.
      constructor; eauto.
      suff : i0 = i by congruence.
      apply WtBRed_embed in h0.
      eauto using unique_sorts_mutual.
    + apply WB_Conv' with (A := Pi A'0 B).
      apply : WB_Lam; eauto using WtBRed_embed with bred.
      apply : Ctx_step; eauto. sfirstorder use:WtBRed_embed.
      apply : WE_Red.
      constructor; eauto.
      apply WtBRed_embed in h0.
      suff : i0 = i by congruence.
      apply WtBRed_embed in hA.
      eauto using unique_sorts_mutual.
  - move => Γ A i B B' M M' N N' hA hB ihB hM ihM hN ihN P B0 /BInv.App_inv.
    move => [A0][B'0][Q'][i0][h0][h1][h2][h3].
    have eA : Γ ⊢ A ≡ A0 by sfirstorder use:βunique.
    have ? : i0 = i by hauto lq:on use:equiv_sort_unique. subst.
    move => [].
    + move => [M0][hM0]?. subst.
      move /ihM : (hM0) => [M''][h4]h5 {ihM}.
      move /ihN : (h2) => [N0][h6]h7 {ihN}.
      (* move /ihA : (h0) => [A''][h8]h9. *)
      have {}h1 : A :: Γ ⊢ B ▻β B'0 ∈ Univ i by
        apply : βCtx_conv; eauto using Equiv_sym with wt.
      move /ihB : (h1)  => [B''][h10]h11 {ihB}.
      exists (App B'' M'' N0). split.
      * apply WB_Conv with (A := B'[N'..]) => //.
        apply WB_App with (i := i) (A := A); eauto.
        apply : βexchange; eauto.
        have : Γ ⊢ M' ∈ Pi A B by hauto lq:on rew:off use:rh_refl_mutual, WtBRed_embed.
        move /WtBRed_embed : hB hA. clear. move => h0 h1 h2. apply : WR_Conv; eauto.
        apply : WE_Red; eauto. constructor; eauto.
        hauto lq:on rew:off use:WB_Conv, Equiv_sym.
        apply : WE_Trans; eauto.
        apply Equiv_sym. apply : WE_Red.
        apply : WR_cong_univ; eauto. sfirstorder use:WtBRed_embed.
        sfirstorder use:WtBRed_embed.
      * apply WB_Conv with (A := B'0[Q'..]).
        eapply WB_App with (A := A) (i := i); eauto.
        apply : βexchange; eauto. move {h5}.
        have hk : Γ ⊢ M ▻β M0 ∈ Pi A B. apply : βexchange; eauto. hauto lq:on use:lh_refl_mutual, WtBRed_embed.
        have {}hk : Γ ⊢ M0 ∈ Pi A B by qauto l:on use:WtBRed_embed, rh_refl_mutual.
        apply : WR_Conv; eauto. apply : WE_Red; eauto using WtBRed_embed with wt.
        apply Equiv_sym.
        apply : WE_Red; eauto.
        eapply WR_cong_univ with (i := i); eauto using exchange, WtBRed_embed.
    + move => [M0][M0'][?][hM0]?. subst.
      have hL : Γ ⊢ Lam A0 M0 ▻β Lam A0 M0' ∈ Pi A0 B.
      econstructor; eauto. sfirstorder use:β_lh_refl.
      hauto lq:on use:WtBRed_embed, lh_refl_mutual.
      move /ihM : (hL) => [M''][hM1]/BInv.Lam_inv {ihM}.
      move => [A'1][M'0][B1][i1][?][hL0][hL1][hL2]hL3. subst.
      rename M'0 into M''.
      (* By uniqueness typing *)
      (* have heq : Γ ⊢ A0 ≡ A by sfirstorder use:βunique. *)
      have : A :: Γ ⊢ B ▻β B'0 ∈ Univ i.
      apply βCtx_conv with (A := A0); by eauto using WtBRed_embed, Equiv_sym with wt.
      move /ihB => [B''][hB0]hB1.
      move /ihN : (h2) => [N''][hN0]hN1.
      move /BInv.Lam_inv : hM => [A'2] [ M'0][ B2] [i2][?] [hA0][hB2][hM2]he. subst.
      move /BInv.Lam_inv : hM1 => [A'3][M'][B3][i3][[? ?]][hA2][hB3][hM3]he'. subst.
      have heq' : Γ ⊢ A ≡ A'2.
      move : hA0 eA. clear.
      move /WtBRed_embed /WE_Exp. by eauto using Equiv_sym, WE_Trans.
      have ? : i2 = i1 by move : hA0 hL0; clear; hauto lq:on use:unique_sorts_mutual, WtBRed_embed. subst.
      have ? : i1 = i by move : h0 hL0; clear; hauto lq:on use:unique_sorts_mutual, WtBRed_embed. subst.
      have ? : i3 = i by move /WtBRed_embed : hA2; move /WtBRed_embed : hA0; clear;
        hauto lq:on use:unique_sorts_mutual, rh_refl_mutual. subst.
      exists M'[N''..].
      split.
      * apply WB_Conv with (A := B'[N'..]); eauto.
        apply WB_Beta with (i := i);
          eauto 4 using exchange, WRs_TransR, Ctx_conv with bred.
        hauto lq:on use:WtBRed_embed, rh_refl_mutual.
        have : A :: Γ ⊢ B' ∈ Univ i by move : hB0; clear; hauto lq:on use:WtBRed_embed, lh_refl_mutual.
        move : heq'. clear. move => h0 h1.
        apply : Ctx_conv; eauto with wt.
        hauto lq:on use:equiv_regularity0 db:wt.
        apply : βexchange; eauto.
        apply : Ctx_conv_simpl; eauto. move {hM3}.
        have {}hM2 : A :: Γ ⊢ M0 ▻ M'0 ∈ B2 by sfirstorder use:Ctx_conv_simpl, Equiv_sym, WtBRed_embed.
        apply : exchange'; eauto.
        have {}hM0 : A :: Γ ⊢ M0 ▻ M0' ∈ B by sfirstorder use:Ctx_conv_simpl, Equiv_sym, WtBRed_embed.
        eapply lh_refl_mutual in hM0.
        apply : WR_Conv; eauto.
        apply : WE_Red; eauto using WtBRed_embed.
        apply : WB_Conv; eauto.
        apply /WE_Red /WtBRed_embed; eauto.
        apply : WE_Trans; eauto.
        apply : WE_Exp. apply WR_cong_univ with (A := A); eauto using WtBRed_embed.
      * rename Q' into N0.
        eapply WB_Conv with (A := B[N0..]); cycle 1.
        apply : WE_Exp. apply : WR_cong_univ; eauto using WtBRed_embed with bred wt.
        have hΓ : ⊢ Γ by sfirstorder use:Wt_Wf_mutual.
        have {}hL2 : A :: Γ ⊢ M0' ▻β M' ∈ B.
        apply βCtx_conv with (A := A0); eauto using Equiv_sym with wt.
        apply : βexchange; eauto.
        apply WtBRed_embed in hM0.
        sfirstorder use:wr_rh_refl.
        apply : βmorphing2; eauto.
        apply βmorphing2_ext. by apply βmorphing2_id. by asimpl.
  - move => Γ A i B M M' N N'  hA hB   hM ihM hN ihN ? T.
    move /BInv.App_inv => [A2]  [B1] [N0'][i0][hA2][hB1][hN'][hB2][].
    + move => [?][hA3]?. subst.
      move /BInv.Lam_inv : hA3 => [A0'][M0'][B'][i1][?][hA3][hB'][hM']heq. subst.
      move /ihM  : hM' {ihM} => [M''][hM0'']hM1''.
      move /ihN : (hN') {ihN} => [N''][hN0'']hN1''.
      have hΓ' : ⊢ Γ by sfirstorder use:Wt_Wf_mutual.
      exists M''[N''..].
      split.
      * apply WB_Conv with (A := B[N'..]); eauto.
        apply : βmorphing2; eauto.
        apply : βexchange; eauto.
        qauto l:on use:wr_rh_refl,WtBRed_embed.
        apply βmorphing2_ext. by apply βmorphing2_id.
        asimpl.
        apply : βexchange;eauto. hauto lq:on use:wr_rh_refl, WtBRed_embed.
        apply : WE_Trans; eauto.
        apply : WE_Exp; eauto. apply : WR_cong_univ; eauto using WtBRed_embed.
      * eapply WB_Conv with (A := B1[N0'..]).
        have ? : i1 = i by move : hA3 hA; clear;
          hauto lq:on rew:off use:WtBRed_embed, unique_sorts_mutual.
        subst.
        have e0 : Γ ⊢ A2 ≡ A by sfirstorder use:βunique.
        have e1 : Γ ⊢ A0' ≡ A by hauto lq:on use:WtBRed_embed db:wt.
        have e2 : Γ ⊢ A2 ≡ A0' by hauto lq:on use:Equiv_sym, WE_Trans.
        have ? : i0 = i by sfirstorder use:equiv_sort_unique. subst.

        apply : WB_Beta; eauto.
        hauto lq:on use:WtBRed_embed, rh_refl_mutual.
        move /WtBRed_embed /wr_rh_refl in hB1.
        sfirstorder use:Ctx_conv_simpl,Equiv_sym.
        (* hM1'' *)
        apply : βCtx_conv; eauto.
        apply : βexchange ; eauto.
        apply WtBRed_embed in hB1.
        apply WE_Red in hB1.
        apply : WR_Conv; eauto.
        apply : Ctx_conv_simpl. apply : wr_lh_refl. apply /WtBRed_embed /hM1''. by apply Equiv_sym.
        apply : βCtx_conv; eauto using Equiv_sym.
        hauto lq:on rew:off use:WB_Conv, Equiv_sym.
        apply : WE_Exp; eauto.
        apply : WR_cong_univ; eauto using WtBRed_embed.
    + move => [_A0][M0'][[<- <-]][hM']?. subst.
      move /ihM  : hM' {ihM} => [M''][hM0'']hM1''.
      move /ihN : (hN') {ihN} => [N''][hN0'']hN1''.
      have hΓ : ⊢ Γ by sfirstorder use:Wt_Wf_mutual.
      have eA : Γ ⊢ A2 ≡ A by sfirstorder use:βunique.
      have ? : i0 = i by sfirstorder use:equiv_sort_unique. subst.
      exists M''[N''..]. split.
      * apply WB_Conv with (A := B[N'..]); eauto.
        apply : βmorphing2; eauto.

        apply βmorphing2_ext. apply βmorphing2_id; eauto. asimpl.
        apply : βexchange; eauto.
        move /WtBRed_embed /wr_rh_refl  in hN'.
        apply β_lh_refl in hN'.
        move /WtBRed_embed /wr_lh_refl in hN0''.
        sfirstorder use:WR_Conv, WR_Conv'.
        apply : WE_Trans; eauto.
        apply : WE_Exp.
        apply : WR_cong_univ; eauto.
        sfirstorder use:WtBRed_embed.
      * apply WB_Conv with (A := B[N0'..]).
        apply : βmorphing2; eauto.
        apply βmorphing2_ext. by apply βmorphing2_id. by asimpl.
        apply : WE_Exp.
        (* apply : WR_cong; eauto using exchange with wt. *)
        apply : WR_cong_univ; eauto using Equiv_sym  with bred.
        hauto lq:on use:WtBRed_embed, Equiv_sym db:bred.
  - hauto lq:on db:wt,bred.
Qed.

Module OExp.
  Inductive R Γ : tm -> tm -> tm -> Prop :=
  | O_Eta a A i B U :
    Γ ⊢ A ∈ Univ i ->
    A :: Γ ⊢ B ∈ Univ i ->
    Γ ⊢ a ∈ Pi A B ->
    Γ ⊢ Pi A B ≡ U ->
    R Γ a  (Lam A (App (B⟨upRen_tm_tm shift⟩) (a⟨shift⟩) (var_tm var_zero))) U.

  Lemma ToPar Γ a b A : OExp.R Γ a b A -> Γ ⊢ a ▻ b ∈ A.
  Proof.
    inversion 1; subst.
    apply : WR_Conv; eauto.
    hauto lq:on db:wt.
  Qed.

  Derive Inversion inv with (forall Γ a b A, R Γ a b A).

  Lemma Conv Γ a b A B :
    R Γ a b A ->
    Γ ⊢ A ≡ B ->
    R Γ a b B.
  Proof.
    elim /inv => //=_.
    move => a0 A0 i B0 U hA0 hB0 ha hPi ? ? ?. subst.
    move : WE_Trans hPi; repeat move/[apply].
    eauto using O_Eta.
  Qed.

  Lemma regularity Γ a b A : R Γ a b A -> Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A.
  Proof.
    qauto l:on use:ToPar, lh_refl_mutual, rh_refl_mutual.
  Qed.


  Lemma O_Eta' Γ a A i B :
    Γ ⊢ A ∈ Univ i ->
    A :: Γ ⊢ B ∈ Univ i ->
    Γ ⊢ a ∈ Pi A B ->
    R Γ a  (Lam A (App (B⟨upRen_tm_tm shift⟩) (a⟨shift⟩) (var_tm var_zero))) (Pi A B).
  Proof.
    move => hA hB ha.
    apply : O_Eta; eauto.
    apply : WE_Red; eauto with wt.
  Qed.

  Lemma commutativity Γ a b c A :
    Γ ⊢ a ▻η b ∈ A ->
    R Γ a c A ->
    exists d, R Γ b d A /\ Γ ⊢ c ▻η d ∈ A.
  Proof.
    move => h. elim /inv => //=_.
    move => a0 A0 i B U hA0 hB ha e *. subst.
    have ? : ⊢ A0 :: Γ by  sfirstorder use:Wt_Wf_mutual.
    eexists. split. econstructor; eauto.
    apply : WR_Conv'; eauto.
    hauto lq:on use:WtExp_embed, wr_rh_refl.
    econstructor; eauto.
    econstructor; eauto using η_lh_refl with eexp.
    have e0 : B = subst_tm (scons (var_tm var_zero) var_tm) (ren_tm (upRen_tm_tm shift) B)by asimpl; rewrite subst_id.
    rewrite {3}e0 => {e0}.
    apply : WE_App. apply : wt_renaming_univ. apply hA0. apply lookup_good_renaming_shift.
    sfirstorder use:Wt_Wf_mutual.
    change (Univ i) with (ren_tm (upRen_tm_tm shift) (Univ i)). apply : wt_η_renaming; eauto with eexp.
    sfirstorder use:η_lh_refl.
    apply good_renaming_up. apply lookup_good_renaming_shift.
    econstructor. apply : wt_renaming_univ; eauto. apply lookup_good_renaming_shift.
    change (Pi A0 ⟨ shift ⟩ B ⟨ upRen_tm_tm shift ⟩) with (ren_tm shift (Pi A0 B)).
    apply : wt_η_renaming; eauto using Equiv_sym with eexp.
    apply lookup_good_renaming_shift.
    constructor=>//. constructor.
  Qed.

End OExp.

Module IExp.
  Inductive R : context -> tm -> tm -> tm -> Prop :=
  | I_Var Γ n A :
    ⊢ Γ ->
    lookup n Γ A ->
    (* ------------- *)
    R Γ (var_tm n) (var_tm n) A

  | I_Univ Γ i :
    ⊢ Γ ->
    (* ----------- *)
    R Γ (Univ i) (Univ i) (Univ (S i))

  | I_Prod Γ i A A' B B' :
    Γ ⊢ A ▻η A' ∈ Univ i ->
    A :: Γ ⊢ B ▻η B' ∈ Univ i ->
    (* ------------------- *)
    R Γ (Pi A B) (Pi A' B') (Univ i)

  | I_Lam Γ A A' i B M M' :
    Γ ⊢ A ▻η A' ∈ Univ i ->
    A :: Γ ⊢ B ▻ B ∈ Univ i ->
    A :: Γ ⊢ M ▻η M' ∈ B ->
    (* ------------------ *)
    R Γ (Lam A M) (Lam A' M') (Pi A B)

  | I_App Γ A i B B' M M' N N' :
    Γ ⊢ A ▻ A ∈ Univ i ->
    A :: Γ ⊢ B ▻η B' ∈ Univ i ->
    Γ ⊢ M ▻η M' ∈ Pi A B ->
    Γ ⊢ N ▻η N' ∈ A ->
    (* ------------------------ *)
    R Γ (App B M N) (App B' M' N') B[N..]


  | I_Conv Γ M N A B :
    R Γ M N A ->
    Γ ⊢ A ≡ B ->
    (* ----------------- *)
    R Γ M N B.

  Lemma ToEPar Γ a b A : R Γ a b A -> Γ ⊢ a ▻η b ∈ A.
  Proof. induction 1; eauto with eexp. Qed.

End IExp.

Module IInv.

  Lemma Prod_inv Γ A B N T (h : IExp.R Γ (Pi A B) N T) :
    exists A' B' i, N = Pi A' B' /\ Γ ⊢ A ▻η A' ∈ Univ i /\ A::Γ ⊢ B ▻η B' ∈ Univ i /\ Γ ⊢ Univ i ≡ T.
  Proof.
    move E : (Pi A B) h => M h.
    move : A B E.
    elim : Γ M N T / h=>//.
    - move => Γ i A A' B B' hA hB A0 B0 [*]. subst.
      exists A',B',i. repeat split => //=.
      hauto lq:on use:Wt_Wf_mutual, IExp.ToEPar, WtExp_embed db:wt.
    - move => Γ M N A B hM ihM e A0 B0 ?. subst.
      spec_refl.
      move : ihM => [A'][B'][i][?][h0][h1]h2. subst.
      exists A', B', i. repeat split => //=.
      eauto using Equiv_sym, WE_Trans.
  Qed.

  Lemma Lam_inv Γ A M N T (h : IExp.R Γ (Lam A M) N T) :
    exists A' M' B i,
      N = Lam A' M' /\
      WtExp Γ A A' (Univ i) /\
        A::Γ ⊢ B ∈ Univ i /\
        WtExp (A::Γ) M M' B /\
        Γ ⊢ Pi A B ≡ T.
  Proof.
    move E : (Lam A M) h => M0 h.
    move : A M E.
    elim : Γ M0 N T / h=>//.
    - move => Γ A A' i B M M' hA hB hM A0 M0 [*]. subst.
      exists A',M',B,i.
      repeat split => //=.
      have : Γ ⊢ Pi A B ▻ Pi A' B ∈ Univ i by hauto lq:on use:WtExp_embed ctrs:WtRed.
      hauto lq:on use:wr_lh_refl, WE_Red.
    - hauto lq:on rew:off db:wt.
  Qed.


  Lemma App_inv Γ P B Q N T (h : IExp.R Γ (App B P Q) N T) :
    exists A B' Q' i,
      Γ ⊢ A ∈ Univ i /\ A::Γ ⊢ B ▻η B' ∈ Univ i /\ Γ ⊢ Q ▻η Q' ∈ A /\
        Γ ⊢ B[Q..] ≡ T /\
        (* App case *)
        (exists P', Γ ⊢ P ▻η P' ∈ Pi A B /\ N = App B' P' Q').
  Proof.
    move E : (App B P Q) h => M h.
    move : B P Q E.
    elim : Γ M N T / h=>//.
    - move => Γ A i B B' M M' N N' hA hB hM hN >[]*. subst.
      exists A, B', N', i.
      repeat split => //.
      apply WtExp_embed in hB.
      apply : WE_Red. apply : wt_morphing_univ; eauto using wr_lh_refl.
      apply : morphing_ext; eauto.  rewrite /lookup_good_morphing.
      asimpl. qauto l:on use:Wt_Wf_mutual ctrs:WtRed.
      asimpl. hauto lq:on use:WtExp_embed, wr_lh_refl.
      qauto l:on use:Wt_Wf_mutual.
      exists M'. split => //.
    - hauto lq:on ctrs:WtEquiv use:Equiv_sym.
  Qed.
End IInv.

Module OExps.
  Inductive R Γ a : tm -> tm -> Prop :=
  | Refl A : Γ ⊢ a ∈ A -> R Γ a a A
  | Step b c A : OExp.R Γ a b A -> R Γ b c A -> R Γ a c A.


  Lemma regularity Γ a b A : R Γ a b A -> Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A.
  Proof.
    induction 1; hauto l:on use:OExp.regularity.
  Qed.

  Lemma transitive Γ a b c A :
    R Γ a b A -> R Γ b c A -> R Γ a c A.
  Proof. induction 1; hauto lq:on ctrs:R. Qed.

  Lemma Once Γ a b A :
    OExp.R Γ a b A ->
    OExps.R Γ a b A.
  Proof.
    move => h. apply : Step; eauto. qauto l:on use:OExp.ToPar, wr_rh_refl, Refl.
  Qed.

  Lemma Conv Γ a b A B :
    R Γ a b A ->
    Γ ⊢ A ≡ B ->
    R Γ a b B.
  Proof. induction 1; hauto l:on ctrs:R,WtRed use:OExp.Conv, WR_Conv. Qed.

  Lemma StepR Γ a b c A : R Γ a b A -> OExp.R Γ b c A -> R Γ a c A.
  Proof. hauto lq:on ctrs:R use:transitive, Once. Qed.

  Lemma commutativity Γ a b c A :
    Γ ⊢ a ▻η b ∈ A ->
    R Γ a c A ->
    exists d, R Γ b d A /\ Γ ⊢ c ▻η d ∈ A.
  Proof.
    move => + h. move : b.
    elim : a c A /h.
    - move => a A ha b hb. exists b.
      split. apply Refl. sfirstorder use:wr_rh_refl, WtExp_embed.
      qauto l:on use:η_lh_refl, WtExp_embed, wr_rh_refl.
    - hauto lq:on ctrs:R use:OExp.commutativity.
  Qed.

End OExps.

Lemma factorization Γ a c A :
  Γ ⊢ a ▻η c ∈ A ->
  exists b, IExp.R Γ a b A /\ OExps.R Γ b c A.
Proof.
  move => h. elim : Γ a c A /h.
  - move => Γ n A hΓ hn.
    exists (var_tm n).
    split. by constructor. apply OExps.Refl.
    by constructor.
  - move => Γ i hΓ.
    eexists. split. by econstructor.
    eauto using OExps.Refl with wt.
  - hauto lq:on ctrs:IExp.R, OExps.R use:IExp.ToEPar, WtExp_embed db:wt, eexp.
  - hauto lq:on ctrs:IExp.R, OExps.R use:IExp.ToEPar, WtExp_embed db:wt, eexp.
  - hauto lq:on ctrs:IExp.R, OExps.R use:IExp.ToEPar, WtExp_embed db:wt, eexp.
  - move => Γ a b A A' i B B' hA [A'' [ihA0 ihA1]] hB [B'' [ihB0 ihB1]] ha [a' [iha0 iha1]].
    have hS : Γ ⊢ Pi A B ▻ Pi A' B' ∈ Univ i
      by hauto lq:on use:WtExp_embed db:wt.
    exists a'. split => //.
    apply : OExps.StepR; eauto.
    apply : OExp.O_Eta; eauto. hauto q:on use:WtExp_embed, wr_rh_refl.
    apply WtExp_embed in hA, hB.
    move  :hA hB. clear. hauto lq:on rew:off use:wr_rh_refl, Ctx_step.
    apply : WR_Red; eauto. hauto l:on use:OExps.regularity.
    by eauto with wt.
  - move => Γ M N A B hM [N'][ih0]ih1 e.
    exists N'. split. hauto lq:on ctrs:IExp.R.
    sfirstorder use:OExps.Conv.
Qed.

Lemma merge Γ a b c A :
  Γ ⊢ a ▻η b ∈ A -> OExp.R Γ b c A -> Γ ⊢ a ▻η c ∈ A.
Proof.
  move => /[swap]. elim/OExp.inv=>//=_.
  move => a0 A0 i B U hA hB hb e ? ? ? h. subst.
  apply : WE_Conv; eauto.
  econstructor; eauto using η_lh_refl, Equiv_sym with eexp.
Qed.

Lemma merge' Γ a b c A :
  Γ ⊢ a ▻η b ∈ A -> OExps.R Γ b c A -> Γ ⊢ a ▻η c ∈ A.
Proof.
  move => + h. move : a. elim : b c A / h; eauto using merge.
Qed.

(* Can I refactor this lemma to talk about eta and iexp instead *)
(* Nope. The IH would become unusable *)
Lemma η_diamond : forall Γ M N A P B, Γ ⊢ M ▻η N ∈ A -> Γ ⊢ M ▻η P ∈ B -> exists Q, Γ ⊢ N ▻η Q ∈ B /\ Γ ⊢ P ▻η Q ∈ A.
Proof.
  move => Γ M N A + + h.
  elim : Γ M N A / h.
  - move => Γ i A hΓ hi P B h.
    exists P. split=>//.
    have h2 : Γ ⊢ var_tm i  ∈ A by eauto with wt.
    apply η_lh_refl with (b := P).
    apply WtExp_embed in h.
    have : Γ ⊢ var_tm i ▻ P ∈ A by eauto using exchange.
    eauto using wr_rh_refl.
  - move => Γ i hΓ P B hr.
    exists P. split => //.
    have h : Γ ⊢ Univ i ∈ Univ (S i) by eauto with wt.
    apply η_lh_refl with (b := P).
    apply WtExp_embed in hr.
    have : Γ ⊢ Univ i ▻ P ∈ Univ (S i) by eauto using exchange.
    eauto using wr_rh_refl.
  - move => Γ i A A' B B' hA ihA hB ihB T U.
    move /factorization.
    move => [T'][h0]h1.
    move /IInv.Prod_inv : h0.
    move => [A'0][B'0][i0][?][h2][h3]h4. subst.
    move : ihA h2;move/[apply]. move => [A''][ihA0]ihA1.
    move : ihB h3;move/[apply]. move => [B''][ihB0]ihB1.
    have e0 : Γ ⊢ A' ≡ A'' by hauto lq:on use:WtExp_embed ctrs:WtEquiv.
    have e1 : Γ ⊢ A'0 ≡ A'' by hauto lq:on use:WtExp_embed ctrs:WtEquiv.
    have e2 : Γ ⊢ A ≡ A' by hauto lq:on use:WtExp_embed ctrs:WtEquiv.
    have e3 : Γ ⊢ A ≡ A'0 by hauto lq:on use:WtExp_embed ctrs:WtEquiv.
    have wtA : Γ ⊢ A ∈ Univ i by hauto lq:on use:WtExp_embed, wr_lh_refl.
    have wtA' : Γ ⊢ A' ∈ Univ i0 by hauto lq:on use:WtExp_embed, wr_lh_refl.
    have ? : i0 = i by move : wtA wtA' e2; clear; hauto lq:on use:equiv_sort_unique. subst.
    have {}ihB0 : A' :: Γ ⊢ B' ▻η B'' ∈ Univ i by sfirstorder use:ηCtx_conv, Equiv_sym.
    have {}ihB1 : A'0 :: Γ ⊢ B'0 ▻η B'' ∈ Univ i by sfirstorder use:ηCtx_conv, Equiv_sym.
    have hPi : Γ ⊢ Pi A' B' ▻η Pi A'' B'' ∈ Univ i by econstructor.
    have hPi0 : Γ ⊢ Pi A'0 B'0 ▻η Pi A'' B'' ∈ Univ i by econstructor.
    have wtPi0 : Γ ⊢ Pi A'0 B'0 ∈ U by hauto l:on use:OExps.regularity.
    have hU : Γ ⊢ U ≡ Univ i by move : hPi0 wtPi0; clear; hauto lq:on use:unique_mutual, WtExp_embed, lh_refl_mutual.
    have {}h1 : OExps.R Γ (Pi A'0 B'0) T (Univ i) by eauto using OExps.Conv.
    move :  OExps.commutativity hPi0 h1; repeat move/[apply].
    move => [d][h0]h1.
    exists d.
    split. apply : WE_Conv; eauto.
    apply : merge'; eauto.
    apply : merge'; eauto.
    apply OExps.Refl. hauto lq:on use:WtExp_embed, wr_rh_refl.
  - move => Γ A A' i B M M' hA ihA hB hM ihM T U.
    move /factorization.
    move => [T'][+]hT1.
    move /IInv.Lam_inv.
    move => [A'0][M'0][B0][i0][?]. subst. move => [h0][h1][h2]h3.
    have hA' : Γ ⊢ A ▻ A' ∈ Univ i by sfirstorder use:WtExp_embed.
    have h0' : Γ ⊢ A ▻ A'0 ∈ Univ i0 by sfirstorder use:WtExp_embed.
    have ? : i0 = i by sfirstorder use:unique_sorts_mutual. subst.
    move : ihA (h0) => /[apply]. move => [A''][ihA0]ihA1.
    move : ihM (h2) => /[apply]. move => [M''][ihM0]ihM1.
    have e0 : Γ ⊢ A ≡  A' by hauto lq:on ctrs:WtEquiv.
    have e1 : Γ ⊢ A ≡  A'0 by hauto lq:on ctrs:WtEquiv.
    have e2 : A :: Γ ⊢ B0 ≡ B by hauto lq:on use:WtExp_embed, wr_rh_refl, unique_mutual.
    have {}ihM0 : A' :: Γ ⊢ M' ▻η M'' ∈ B by sauto lq:on use:ηCtx_conv, Equiv_sym.
    have hLam : Γ ⊢ Lam A' M' ▻η Lam A'' M'' ∈ Pi A' B. econstructor; eauto.
    sfirstorder use:Ctx_conv_simpl, Equiv_sym.
    have {}ihM0 : A'0 :: Γ ⊢ M'0 ▻η M'' ∈ B by sauto lq:on use:ηCtx_conv, Equiv_sym.
    have hLam' : Γ ⊢ Lam A'0 M'0 ▻η Lam A'' M'' ∈ Pi A'0 B. econstructor; eauto.
    sfirstorder use:Ctx_conv_simpl, Equiv_sym.
    have hPi0 : Γ ⊢ Pi A B ▻ Pi A' B ∈ Univ i. apply WtExp_embed.
    econstructor; eauto using η_lh_refl.

    have hPi1 : Γ ⊢ Pi A B ▻ Pi A'0 B ∈ Univ i. apply WtExp_embed.
    econstructor; eauto using η_lh_refl.

    have {}hLam : Γ ⊢ Lam A' M' ▻η Lam A'' M'' ∈ Pi A B
      by hauto lq:on rew:off use:WE_Conv,WE_Red,WE_Exp.

    have {}hLam' : Γ ⊢ Lam A'0 M'0 ▻η Lam A'' M'' ∈ Pi A B
      by hauto lq:on rew:off use:WE_Conv,WE_Red,WE_Exp.

    have wt0 : Γ ⊢ Lam A'' M'' ∈ Pi A B by
      qauto l:on use:wr_rh_refl, WtExp_embed.

    have wt1 : Γ ⊢ Lam A M ∈ Pi A B by
      qauto l:on use:wr_lh_refl, WtExp_embed ctrs:WtRed.

    have wt2 : Γ ⊢ Lam A M ▻ Lam A'0 M'0 ∈ Pi A B0
      by hauto lq:on ctrs:WtExp use:WtExp_embed.
    have e3 : Γ ⊢ Pi A B ≡ Pi A B0
      by hauto lq:on rew:off use:unique_mutual, lh_refl_mutual.
    have e4 : Γ ⊢ U ≡ Pi A B by
      hauto lq:on rew:off use:WE_Trans, Equiv_sym.
    have {hT1} : OExps.R Γ (Lam A'0 M'0) T (Pi A B)
      by qauto l:on use:OExps.Conv, Equiv_sym, WE_Trans.
    move : OExps.commutativity hLam'. repeat move/[apply].
    move => [Q][hQ0]hQ1.
    exists Q. split. apply : WE_Conv; last by apply /Equiv_sym /e4.
    apply : merge'; eauto.
    done.
  - move => Γ A i B B' M M' N N' hA hB ihB hM ihM hN ihN u T.
    move /factorization.
    move => [u' [h0 h1]].
    move /IInv.App_inv : (h0).
    move => [A'0][B'0][N'0][i0][h2][h3][h4][h5][M'0][h6]?. subst.
    have eA : Γ ⊢ A'0 ≡ A
      by qauto l:on use:WtExp_embed, unique_mutual, wr_lh_refl.
    move : ihM (h6) => /[apply].
    move => [M''][ihM0]ihM1.
    have ? : i0 = i by sfirstorder use:equiv_sort_unique. subst.
    have {}h3 : A :: Γ ⊢ B ▻η B'0 ∈ Univ i by
      move : h3 eA; clear; sfirstorder use:Equiv_sym, ηCtx_conv.
    move : ihB (h3) => /[apply].
    move => [B''][ihB0]ihB1.
    move : ihN (h4) => /[apply].
    move => [N''][ihN0]ihN1.
    have ePi : Γ ⊢ Pi A'0 B ≡ Pi A B by
      move : hM h6; clear;  qauto l:on use:unique_mutual, wr_lh_refl, WtExp_embed.

    have {}ihM0 : Γ ⊢ M' ▻η M'' ∈ Pi A B by sfirstorder use:WE_Conv, Equiv_sym.

    have hApp0 : Γ ⊢ App B' M' N' ▻η App B'' M'' N'' ∈  B[N..].
    apply : WE_Conv.
    eapply WE_App with (A := A); eauto.
    apply : ηexchange''; eauto.
    apply : WR_Red; eauto using wr_rh_refl, WtExp_embed.
    by constructor; eauto using WtExp_embed, Equiv_sym.
    by apply : WE_Conv; eauto.
    apply : WE_Exp; eauto. by apply : WR_cong_univ; eauto using WtExp_embed.

    have hApp1 : Γ ⊢ App B'0 M'0 N'0 ▻η App B'' M'' N'' ∈  B[N..].
    apply : WE_Conv.
    apply WE_App with (A := A) (i := i); eauto.
    apply : ηexchange''; eauto.
    apply WR_Red with (i := i) (A := Pi A B); eauto using wr_lh_refl, WtExp_embed.
    by constructor; eauto using WtExp_embed, Equiv_sym.
    apply : WE_Exp; eauto. by apply : WR_cong_univ; eauto using WtExp_embed, WR_Conv.

    have {h1} : OExps.R Γ (App B'0 M'0 N'0) u B[N..]
      by sfirstorder use:OExps.Conv, Equiv_sym.
    move : OExps.commutativity hApp1. repeat move/[apply].
    move => [d][hh0]hh1.
    exists d. split => //=.
    by eauto using merge', WE_Conv.
  - move => Γ a b A A' i B B' hA ihA hB ihB ha iha a' U /[dup] h {}/iha.
    move => [c [ihc0 ihc1]].
    have wtA' : Γ ⊢ A' ∈ Univ i by qauto l:on use:WtExp_embed, wr_rh_refl.
    have hΓ' : ⊢ A' :: Γ by qauto l:on db:wt.
    have e : Γ ⊢ Pi A B ≡ U
      by qauto l:on use:WtExp_embed, wr_rh_refl, unique_mutual, lh_refl_mutual.
    exists (Lam A' (App B' ⟨ upRen_tm_tm shift ⟩ c ⟨ shift ⟩ (var_tm var_zero))). repeat split => //.
    apply WE_Conv with (A := Pi A' B').
    apply : WE_Lam; eauto using η_lh_refl, wr_rh_refl, WtExp_embed.
    apply : wr_rh_refl. apply WtExp_embed. apply : ηCtx_step; eauto using WtExp_embed.
    eapply WE_App' with (A := ren_tm shift A). by asimpl; rewrite subst_id.
    apply : wt_renaming_univ; eauto using wr_lh_refl, WtExp_embed.
    apply lookup_good_renaming_shift.
    apply : η_lh_refl.
    apply : wt_renaming_univ; eauto using WtExp_embed, wr_rh_refl, η_lh_refl.
    apply good_renaming_up.
    apply lookup_good_renaming_shift.
    econstructor. apply : wt_renaming_univ; eauto using WtExp_embed.
    apply lookup_good_renaming_shift.
    change (Pi _ _) with (ren_tm shift (Pi A B')).
    apply : wt_η_renaming; eauto; cycle 1. apply lookup_good_renaming_shift.
    apply : WE_Conv; eauto. apply /Equiv_sym /WE_Trans; eauto.
    apply : WE_Exp; eauto. apply WtExp_embed. constructor; eauto.
    hauto lq:on rew:off use:η_lh_refl, wr_lh_refl, WtExp_embed.
    apply : η_lh_refl.
    apply : WR_Exp.
    constructor; eauto. constructor. apply : wt_renaming_univ; eauto.
    eauto using WtExp_embed. apply lookup_good_renaming_shift.
    apply : WE_Trans; eauto.
    apply : WE_Exp. apply WtExp_embed. econstructor; eauto.
    apply WE_Eta with (i := i); eauto.
  - move => Γ M N A B hM ihM eAB M' U {}/ihM.
    hauto lq:on db:eexp.
Qed.
