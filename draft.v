

Module Type T1.
  Parameter A : Set.
End T1.


Module M1 : T1.
  Definition A : Set := nat.
End M1.



