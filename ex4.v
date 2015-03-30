Definition tautology : forall P : Prop, P -> P
  := fun (P:Prop)(H:P) => H.

Definition Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P
  := fun (P Q:Prop)(H0:~Q /\ (P -> Q))(H1:P) =>
       match H0 with
       | conj H2 H3 => H2 (H3 H1)
       end.

Definition Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q
  := fun (P Q:Prop)(H0:(P \/ Q))(H1:~P) =>
       match H0 with
       | or_introl H2 => False_ind Q (H1 H2)
       | or_intror H3 => H3
       end.

Definition tautology_on_Set : forall A : Set, A -> A
  := fun(A:Set)(H0:A) => H0.

Definition Modus_tollens_on_Set : forall A B : Set, (B -> Empty_set) * (A -> B) -> (A -> Empty_set)
  := fun(A B:Set)(H0:(B -> Empty_set) * (A -> B))(H1:A) =>
       match H0 with
       | pair H2 H3 => H2 (H3 H1)
       end.

Definition Disjunctive_syllogism_on_Set : forall A B : Set, (A + B) -> (A -> Empty_set) -> B
  := fun(A B:Set)(H0:(A + B))(H1:A -> Empty_set) =>
       match H0 with
       | inl H2 => B (H1 H2)
       | inr H3 => H3
       end.
