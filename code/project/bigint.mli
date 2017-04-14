(* $Id: bigint.mli,v 1.1 2011-04-26 13:39:18-07 - - $ *)
(* This is the interface class.

*)
module Bigint : sig
   type bigint                                   (*type definition*)
   val bigint_of_string : string -> bigint       (*val is a function type*)
   val string_of_bigint : bigint -> string       (*add int>int>int : addition takes in two integers and returns an integer *)
   val add : bigint -> bigint -> bigint          (*given def add (x,y) : x+y (int>int>int) say you want to def add3 (x) : (x+3) (int>int)*)
   val sub : bigint -> bigint -> bigint          (*def add3: add 3 _ (int>int) (this is an ex. of currying) or def add3(x) : add 3 x (int>int)*)
   val mul : bigint -> bigint -> bigint          
   val div : bigint -> bigint -> bigint
   val rem : bigint -> bigint -> bigint
   val pow : bigint -> bigint -> bigint
   val zero : bigint                              (*doesn't take any parameters and returns a bigint *)
end

