open Blenses
open Regexcontext
open Lenscontext

val perm_canonizer : Canonizer.t list -> Canonizer.t -> Canonizer.t

val synth : Bvalue.t -> Bvalue.t -> Bvalue.t -> RegexContext.t -> LensContext.t -> 
						Info.t * MLens.t