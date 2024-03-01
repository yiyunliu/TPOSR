tm : Type
nat : Type

Univ : nat -> tm
Lam : tm -> (tm -> tm) -> tm
App : tm -> (tm -> tm) -> tm -> tm -> tm
Pi : tm -> (tm -> tm) -> tm
