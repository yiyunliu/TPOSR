tm : Type
nat : Type

Univ : nat -> tm
Lam : tm -> (bind tm in tm) -> tm
App : tm -> (bind tm in tm) -> tm -> tm -> tm
Pi : tm -> (bind tm in tm) -> tm
