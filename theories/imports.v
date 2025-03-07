From Coq Require Export ssreflect ssrbool.
From Coq Require Export Logic.PropExtensionality
  (propositional_extensionality) Program.Basics (const) FunInd.
From Equations Require Export Equations.
From Ltac2 Require Export Ltac2.
From Hammer Require Export Tactics.
Require Export Psatz.

Set Default Proof Mode "Classic".

Global Set Warnings "-notation-overridden".
Require Export Autosubst2.syntax Autosubst2.unscoped Autosubst2.core.

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity) : subst_scope.
Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.
Import List.ListNotations.

Global Open Scope list_scope.
Global Open Scope subst_scope.
