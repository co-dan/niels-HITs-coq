Ltac hrecursion target rec :=
  generalize dependent target;
  match goal with
  | [ |- forall target, ?P] => 
    match type of rec with
    | forall Y _, forall x, Y x =>
      unshelve refine (rec (fun target => P) _)
    | forall Y _ _, forall x, Y x  =>
      unshelve refine (rec (fun target => P) _ _)
    | forall Y _ _ _, forall x, Y x  =>
      unshelve refine (rec (fun target => P) _ _ _)
    | forall Y _ _ _ _, forall x, Y x  =>
      unshelve refine (rec (fun target => P) _ _ _ _)
    | forall Y _ _ _ _ _, forall x, Y x  =>
      unshelve refine (rec (fun target => P) _ _ _ _ _)
    | forall Y _ _ _ _ _ _, forall x, Y x  =>
      unshelve refine (rec (fun target => P) _ _ _ _ _ _)
    | forall Y _ _ _ _ _ _ _, forall x, Y x  =>
      unshelve refine (rec (fun target => P) _ _ _ _ _ _ _)
    | forall Y _, Y =>
      unshelve refine (rec P)
    | forall Y _ _, Y  =>
      unshelve refine (rec P _)
    | forall Y _ _ _, Y =>
      unshelve refine (rec P _ _)
    | forall Y _ _ _ _, Y  =>
      unshelve refine (rec P _ _ _)
    | forall Y _ _ _ _ _, Y  =>
      unshelve refine (rec P _ _ _ _)
    | forall Y _ _ _ _ _ _, Y =>
      unshelve refine (rec P _ _ _ _ _)
    | forall Y _ _ _ _ _ _ _, Y =>
      unshelve refine (rec P _ _ _ _ _ _)
    end
  end.

