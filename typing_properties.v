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
