Require Export typing.

Lemma here' : forall {A Γ T}, T = A ⟨shift⟩ ->  lookup 0 (A :: Γ) T.
Proof. move => > ->. by apply here. Qed.

Lemma there' : forall {n A Γ B T}, T = A ⟨shift⟩ ->
      lookup n Γ A -> lookup (S n) (B :: Γ) T.
Proof. move => > ->. by apply there. Qed.

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

Lemma equiv_renaming Γ A B (h : Γ ⊢ A ≡ B) :
  forall ξ Δ, lookup_good_renaming ξ Γ Δ -> ⊢ Δ -> Δ ⊢ A⟨ξ⟩ ≡ B⟨ξ⟩.
Proof.
  elim : A B / h; hauto q:on ctrs:WtEquiv use:wt_renaming_mutual.
Qed.

Definition lookup_good_morphing ρ0 ρ1 Γ Δ :=
  forall n A, lookup n Γ A -> Δ ⊢ ρ0 n ▻ ρ1 n ∈ A[ρ0].

Lemma lookup_good_renaming_shift A Δ:
  lookup_good_renaming ↑ Δ (A :: Δ).
Proof. rewrite /lookup_good_renaming => >. apply there. Qed.

Lemma subst_ren_factor A ρ ξ :  A[ρ >> ren_tm ξ ] = A[ρ]⟨ξ⟩.
Proof. by asimpl. Qed.

Lemma good_morphing_up ρ0 ρ1 k Γ Δ A
  (h : lookup_good_morphing ρ0 ρ1 Γ Δ) :
  Δ ⊢ A[ρ0] ▻ A[ρ1] ∈ Univ k ->
  lookup_good_morphing (up_tm_tm ρ0) (up_tm_tm ρ1) (A :: Γ) (A [ρ0] :: Δ).
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
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ρ0 ρ1 Δ,
        lookup_good_morphing ρ0 ρ1 Γ Δ -> Wf Δ -> Δ ⊢ a[ρ0] ▻ a[ρ1] ∈ A[ρ0] ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> forall ρ0 ρ1 Δ,
        lookup_good_morphing ρ0 ρ1 Γ Δ -> Wf Δ -> Δ ⊢ a[ρ0] ▻+ a[ρ1] ∈ A[ρ0] ) /\
  (forall Γ, ⊢ Γ -> forall ρ0 ρ1 Δ, lookup_good_morphing ρ0 ρ1 Γ Δ -> Wf Δ -> lookup_good_morphing ρ0 ρ0 Γ Δ).
Proof.
  apply wt_mutual_ind; eauto with wt.
  8 : {
    hauto q:on inv:lookup unfold:lookup_good_morphing.
  }
  8 : {
    move => Γ A B i hA ihA ρ0 ρ1 Δ hρ hΔ.
    rewrite /lookup_good_morphing => k A0.
    elim /lookup_inv => h.
    - move => > ? []*. subst.
      rewrite /lookup_good_morphing in hρ.
      move : h.
      move /hρ.
      asimpl.

  }
  - hauto l:on unfold:lookup_good_morphing db:wt.
  - hauto q:on use:good_morphing_up db:wt.
  - move => Γ A A' i B M M' hA ihA hB ihB hM ihM ρ0 ρ1 Δ hρ hΔ /=.
    apply : WR_Lam; eauto with wt.
    apply ihB. apply : good_morphing_up; auto.

Lemma left_hand_reflexivity_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> Γ ⊢ a ▻ a ∈ A ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ a ▻ a ∈ A ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind=>//; eauto with wt.
  move => *. apply : WR_App.
  sfirstorder.
  best.
