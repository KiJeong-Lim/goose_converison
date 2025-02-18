(* autogenerated from io *)
From New.golang Require Import defn.

Module io.
Section code.
Context `{ffi_syntax}.


Axiom ErrShortWrite'init : val.

Axiom errInvalidWrite'init : val.

Axiom ErrShortBuffer'init : val.

Axiom EOF'init : val.

Axiom ErrUnexpectedEOF'init : val.

Axiom ErrNoProgress'init : val.

Definition Reader : go_type := interfaceT.

Definition Writer : go_type := interfaceT.

Axiom errWhence'init : val.

Axiom errOffset'init : val.

Axiom Discard'init : val.

Axiom blackHolePool'init : val.

Axiom ErrClosedPipe'init : val.

Definition pkg_name' : go_string := "io".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [].

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  (ErrShortWrite'init #());;;
      do:  (errInvalidWrite'init #());;;
      do:  (ErrShortBuffer'init #());;;
      do:  (EOF'init #());;;
      do:  (ErrUnexpectedEOF'init #());;;
      do:  (ErrNoProgress'init #());;;
      do:  (errWhence'init #());;;
      do:  (errOffset'init #());;;
      do:  (Discard'init #());;;
      do:  (_'init #());;;
      do:  (blackHolePool'init #());;;
      do:  (_'init #());;;
      do:  (_'init #());;;
      do:  (ErrClosedPipe'init #()))
      ).

End code.
End io.
