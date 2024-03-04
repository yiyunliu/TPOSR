Require Export typing.

Lemma here' : forall {A Γ T}, T = A ⟨shift⟩ ->  lookup 0 (A :: Γ) T.
Proof. move => > ->. by apply here. Qed.

Lemma there' : forall {n A Γ B T}, T = A ⟨shift⟩ ->
      lookup n Γ A -> lookup (S n) (B :: Γ) T.
Proof. move => > ->. by apply there. Qed.

Lemma WR_Conv Γ a b A B : Γ ⊢ a ▻ b ∈ A -> Γ ⊢ A ≡ B -> Γ ⊢ a ▻ b ∈ B.
Proof.
  move => + h. elim : A B / h; eauto with wt.
Qed.

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
  Γ ⊢ App A B M N ▻ App A' B' M' N' ∈ T.
Proof. move =>> ->. apply WR_App. Qed.

Lemma WR_Beta' Γ A i A' A0 B M M' N N' P T :
  P = M'[N'..] ->
  T = B[N..] ->
  Γ ⊢ A ▻ A ∈ Univ i ->
  Γ ⊢ A' ▻ A' ∈ Univ i ->
  Γ ⊢ A0 ▻+ A ∈ Univ i ->
  Γ ⊢ A0 ▻+ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  A :: Γ ⊢ M ▻ M' ∈ B ->
  Γ ⊢ N ▻ N' ∈ A ->
  (*----------------------  *)
  Γ ⊢ App A' B (Lam A M) N ▻ P ∈ T.
Proof. move =>> -> ->. apply WR_Beta. Qed.

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
  - move => */=. apply : WR_App'; eauto using good_renaming_up with wt.
    by asimpl.
  - move => *. apply : WR_Beta';
      (* The two eautos is *NOT* a typo. Need to suppress the use of
      wt constructors to avoid prematurely instantiating ▻+ with the
      One constructor *)
      eauto using good_renaming_up;
      eauto using good_renaming_up with wt.
    by asimpl.
    by asimpl.
Qed.

Definition lookup_good_morphing ρ Γ Δ :=
  forall n A, lookup n Γ A -> Δ ⊢ ρ n ▻ ρ n ∈ A[ρ].

Lemma lookup_good_renaming_shift A Δ:
  lookup_good_renaming ↑ Δ (A :: Δ).
Proof. rewrite /lookup_good_renaming => >. apply there. Qed.

Lemma subst_ren_factor A ρ ξ :  A[ρ >> ren_tm ξ ] = A[ρ]⟨ξ⟩.
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
    apply : WR_App'; eauto. by asimpl. qauto l:on use:good_morphing_up db:wt.
  - move => Γ A i A' A0 B M M' N N' hA ihA hA' ihA' hA00 ihA00 hA01 ihA01 hB ihB hM ihM hN ihN ρ Δ hρ hΔ /=.
    apply : WR_Beta'; eauto; cycle 1.
    by asimpl.
    hauto lq:on use:good_morphing_up db:wt.
    hauto lq:on use:good_morphing_up db:wt.
    by asimpl.
Qed.

Lemma equiv_renaming Γ A B (h : Γ ⊢ A ≡ B) :
  forall ξ Δ, lookup_good_renaming ξ Γ Δ -> ⊢ Δ -> Δ ⊢ A⟨ξ⟩ ≡ B⟨ξ⟩.
Proof.
  elim : A B / h; hauto q:on ctrs:WtEquiv use:wt_renaming_mutual.
Qed.

Lemma wr_morphing :
  forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻ b[ρ] ∈ A[ρ].
Proof. apply wt_morphing_mutual. Qed.

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
    apply WR_Conv with (A := A' ⟨↑⟩).
    hauto q:on ctrs:WtRed, lookup.
    apply : equiv_renaming=>//; last by apply lookup_good_renaming_shift. exact h.
  + move => n A1 Γ0 B0 ? ? []*. subst.
    asimpl.
    change (var_tm (↑ n)) with ((var_tm n)⟨↑⟩).
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
  move => Γ A i A' A0 B M M' N N' h0 _  h1 _ hA00 ihA00 hA01 ihA01 hB ihB hM ihM hN ihN.
  have hequiv : Γ ⊢ A' ≡ A by eauto using Conv_Equiv.
  have /Equiv_sym hequiv_s := hequiv.
  apply : WR_App; eauto 1 with wt.
  - move => [:tr0].
    move : ihB. move/wr_morphing /(_ var_tm). asimpl. apply; last by abstract : tr0; eauto with wt.
    apply lookup_good_id; eauto.
  - apply : WR_Conv.
    + apply : WR_Lam; eauto.
    + have : Γ ⊢ Pi A0 B ▻+ Pi A B ∈ Univ i by eauto using lh_refl_helper.
      move /Ctx_conv /(_ ltac:(sfirstorder) ltac:(hauto lq:on db:wt)) in hB.
      have : Γ ⊢ Pi A0 B ▻+ Pi A' B ∈ Univ i by eauto using lh_refl_helper.
      move => /wrs_Equiv + /wrs_Equiv /Equiv_sym.
      move /[swap]. apply WE_Trans.
  - apply : WR_Conv; eauto.
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
  - move => *.
    apply : WR_App'; eauto. by asimpl. qauto l:on use:good_morphing2_up db:wt.
  - move => Γ A i A' A0 B M M' N N' hA ihA hA' ihA' hA00 ihA00 hA01 ihA01 hB ihB hM ihM hN ihN ρ0 ρ1 Δ hρ hΔ /=.
    apply WR_Beta' with (M' := M'[up_tm_tm ρ1]) (N' := N'[ρ1]) (A0 := A0[ρ0]) (i := i); eauto 3.
    + by asimpl.
    + by asimpl.
    + qauto l:on db:wt use:lh_refl_mutual.
    + hauto lq:on rew:off db:wt use:lh_refl_mutual.
    + sfirstorder use:lookup_good_morphing2_lh_refl.
    + sfirstorder use:lookup_good_morphing2_lh_refl.
    + hauto lq:on use:good_morphing2_up, lookup_good_morphing2_lh_refl db:wt.
    + hauto lq:on use:good_morphing2_up, lookup_good_morphing2_lh_refl db:wt.
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
  - move => Γ A i A' A0 B M M' N N' hA ihA.
