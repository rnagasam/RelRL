(** Automatic collision detection and renaming for generated identifiers
    
    This module provides a collision registry system that:
    - Collects all user-defined identifiers from the annotated program
    - Tracks identifiers generated during translation
    - Automatically generates fresh identifiers by appending numeric suffixes
    
    This enables WhyRel to freely rename generated identifiers without 
    restricting user-defined identifiers in .rl files, removing the need for
    identifier usage restrictions.
*)

(** The collision registry type *)
type collision_registry

(** Create a new empty collision registry *)
val create : unit -> collision_registry

(** Collect all user-provided identifiers from an annotated program *)
val collect_user_identifiers : Annot.penv -> Set.Make(String).t

(** Initialize a registry with user identifiers from the annotated program *)
val init_with_penv : collision_registry -> Annot.penv -> unit

(** Generate a fresh identifier that avoids collisions
    
    This function ensures the returned identifier doesn't collide with:
    - Any user-defined identifiers
    - Any previously generated identifiers in this registry
    
    If collisions are detected, numeric suffixes are appended until a
    unique identifier is found.
*)
val mk_fresh_ident : collision_registry -> string -> string
