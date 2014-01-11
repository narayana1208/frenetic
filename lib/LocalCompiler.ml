open Core.Std
open Sexplib.Conv

open SDN_Types

module type FIELDMAP = sig
  type t = (field * fieldVal) list
  module Set : Set.S with type Elt.t = t
  val to_string : ?init:string -> ?sep:string -> t -> string
  val set_to_string : ?init:string -> ?sep:string -> Set.t -> string
  val compare : t -> t -> int    
  val empty : t
  val mk : field -> fieldVal -> t
  val is_empty : t -> bool
  val seq : t -> t -> t option
  val diff : t -> t -> t
  val subseteq : t -> t -> bool
end

module FieldMap : FIELDMAP = struct

  type t = (field * fieldVal) list sexp_opaque with sexp
        
  let to_string ?init:(init="") ?sep:(sep="=") (x:t) : string =
    match x with 
      | [] -> init
      | _ -> 
        List.fold x ~init:""
          ~f:(fun acc (f, v) ->
            Printf.sprintf "%s%s%s%s"
              (if acc = "" then "" else ", " ^ acc)
              (Pretty.string_of_field f)
              sep
              (Pretty.value_to_string v))

  type this_t = t with sexp

  let compare (x:t) (y:t) : int = 
    List.compare x y 
      ~cmp:(fun (f1,v1) (f2,v2) -> 
          let cmp = compare f1 f2 in 
          if cmp <> 0 then cmp 
          else Pervasives.compare v1 v2)

  module Set = Set.Make(struct
    type t = this_t with sexp
    let compare = compare
  end)

  let set_to_string ?init:(init="") ?sep:(sep="=") (s:Set.t) : string =
    Printf.sprintf "{%s}"
      (Set.fold s
         ~init:""
         ~f:(fun acc x -> 
           Printf.sprintf "%s%s"
             (if acc = "" then "" else acc ^ ", ")
             (to_string ~init:init ~sep:sep x)))

  let empty : t = 
    []

  let is_empty (x:t) : bool = 
    match x with 
      | [] -> true
      | _ -> false

  let mk (f:field) (v:fieldVal) : t = 
    [(f,v)]
      
  let rec subseteq (x:t) (y:t) : bool =  
    match x,y with 
      | _,[] -> true
      | [],_::_ -> false
      | (fx,vx)::xrest, (fy,vy)::yrest -> 
        let cmp = Pervasives.compare fx fy in 
        if cmp = 0 then 
          vx = vy && subseteq xrest yrest
        else if cmp < 0 then 
          subseteq xrest y
        else (* cmp > 0 *)
          false

  let rec seq (x:t) (y:t) : t option = 
    let map_option f = function
      | None -> None
      | Some x -> Some (f x) in 
    let rec loop x y k = 
      match x,y with 
        | _,[] -> 
          k (Some x)
        | [],_::_ -> 
          k (Some y)
        | (fx,vx)::xrest, (fy,vy)::yrest -> 
          let cmp = Pervasives.compare fx fy in 
          if cmp = 0 then 
            loop xrest yrest 
              (fun o -> k (map_option (fun l -> (fx,vx)::l) o))
          else if cmp < 0 then 
            loop xrest y 
              (fun o -> k (map_option (fun l -> (fx,vx)::l) o))
          else (* cmp > 0 *)
            loop x yrest
              (fun o -> k (map_option (fun l -> (fy,vy)::l) o)) in 
    loop x y (fun o -> o)

  let diff (x:t) (y:t) : t = 
    let rec loop x y k = 
      match x,y with 
        | _,[] -> 
          k x
        | [],_::_ -> 
          k x
        | (fx,vx)::xrest, (fy,vy)::yrest -> 
          let cmp = Pervasives.compare fx fy in 
          if cmp = 0 then 
            loop xrest yrest k 
          else if cmp < 0 then 
            loop xrest y (fun l -> (fx,vx)::l)
          else (* cmp > 0 *)
            loop x yrest k in 
    loop x y (fun o -> o)
end

module type ACTION = sig
  type t = FieldMap.t
  module Set : Set.S with type Elt.t = t
  type group 
  val to_string : t -> string
  val set_to_string : Set.t -> string
  val group_to_string : group -> string
  val mk : field -> fieldVal -> t
  val seq : t -> t -> t option
  val diff : t -> t -> t
  val group_mk : Set.t -> group
  val group_union : group -> group -> group
  val group_cross : group -> group -> group
  val id : Set.t 
  val drop : Set.t 
  val is_id : Set.t -> bool
  val is_drop : Set.t -> bool
  val group_id : group
  val group_drop : group
  val group_is_id : group -> bool
  val group_is_drop : group -> bool
  val to_netkat : t -> Types.policy
  val set_to_netkat : Set.t -> Types.policy
  val group_to_netkat : group -> Types.policy
end

module Action : ACTION = struct

  type t = FieldMap.t

  module SetSet = Set.Make(FieldMap.Set)

  module Set = FieldMap.Set

  type group = Set.t list

  let to_string : t -> string = 
    FieldMap.to_string ~init:"" ~sep:":="

  let set_to_string : Set.t -> string = 
    FieldMap.set_to_string ~init:"" ~sep:":="

  let group_to_string (g:group) : string = 
    List.fold g
      ~init:""
      ~f:(fun acc s -> 
           Printf.sprintf "%s%s"
             (if acc = "" then "" else acc ^ "; ")
             (set_to_string s))

  let mk (f:field) (v:VInt.t) : t = 
    FieldMap.mk f v

  let seq : t -> t -> t option = 
    FieldMap.seq

  let diff : t -> t -> t = 
    FieldMap.diff

  let group_mk (s:Set.t) : group = 
    [s]

  let group_union (g1:group) (g2:group) : group = 
    let ss = 
      List.fold g2
        ~init:SetSet.empty
        ~f:SetSet.add in 
    let rec loop g ss k = 
      match g with 
        | [] -> k g2
        | s::grest -> 
          loop grest ss (fun l -> k (s::l)) in 
    loop g1 ss (fun l -> l)

  let group_cross (g1:group) (g2:group) : group = 
    fst (List.fold_right g1
           ~init:([],SetSet.empty)
           ~f:(fun s1i acc -> 
                 List.fold_right g2
                   ~init:acc
                   ~f:(fun s2j acc -> 
                         let g,ss = acc in 
                         let s1is2j = Set.union s1i s2j in 
                         if SetSet.mem ss s1is2j then acc
                         else (s1is2j::g, SetSet.add ss s1is2j))))

  let id : Set.t = 
    Set.singleton (FieldMap.empty)

  let drop : Set.t = 
    Set.empty

  let is_id (s:Set.t) : bool = 
    Set.length s = 1 && 
    match Set.min_elt s with 
      | None -> false
      | Some a -> FieldMap.is_empty a

  let is_drop (s:Set.t) : bool = 
    Set.is_empty s


  let group_id : group = 
    [id]
      
  let group_drop : group = 
    [drop]

  let group_is_id (g:group) : bool = 
    match g with 
      | [s] -> is_id s
      | _ -> false

  let group_is_drop (g:group) : bool = 
    match g with 
      | [s] -> is_drop s
      | _ -> false

  let to_netkat (a:t) : Types.policy =
    let f pol (f,v)  = 
      let pol' = Types.Mod (Types.Header f, v) in 
      if f =  InPort then 
	Types.Seq (pol, pol') 
      else 
	Types.Seq (pol', pol) in
    match a with 
      | [] -> 
        Types.Filter Types.True
      | (h,v)::arest -> 
        List.fold arest
          ~init:(Types.Mod(Types.Header h,v))
          ~f:f
	
  let set_to_netkat (s:Set.t) : Types.policy =
    if Set.is_empty s then
      Types.Filter Types.False
    else
      let f pol a = Types.Par (pol, to_netkat a) in
      let a = Set.min_elt_exn s in
      let s' = Set.remove s a in
      Set.fold s' ~f:f ~init:(to_netkat a)

  let group_to_netkat (g:group) : Types.policy =
    match g with
      | [] ->
        Types.Filter Types.False
      | [s] ->
        set_to_netkat s
      | s::g' ->
        let f pol s = Types.Choice (pol, set_to_netkat s) in
        List.fold g' ~init:(set_to_netkat s) ~f:f
end

module type PATTERN = sig
  type t = FieldMap.t
  module Set : Set.S with type Elt.t = t
  val to_string : t -> string
  val set_to_string : Set.t -> string
  val compare : t -> t -> int
  val mk : field -> fieldVal -> t
  val seq : t -> t -> t option
  val diff : t -> t -> t
  val subseteq : t -> t -> bool
  val tru : t
  val to_netkat : t -> Types.pred
  val set_to_netkat : Set.t -> Types.pred
end

module Pattern : PATTERN = struct

  type t = FieldMap.t

  module Set = FieldMap.Set

  let to_string : t -> string = 
    FieldMap.to_string ~init:"" ~sep:":="

  let set_to_string : Set.t -> string = 
    FieldMap.set_to_string ~init:"" ~sep:":="

  let compare : t -> t -> int = 
    FieldMap.compare

  let mk (f:field) (v:VInt.t) = 
    FieldMap.mk f v

  let seq : t -> t -> t option = 
    FieldMap.seq
      
  let diff : t -> t -> t = 
    FieldMap.diff

  let subseteq : t -> t -> bool = 
    FieldMap.subseteq
      
  let tru : t = 
    FieldMap.empty

  let to_netkat (x:t) : Types.pred =
    let rec loop x k = 
      match x with 
        | [] -> 
          k Types.True
        | [(f,v)] -> 
          k (Types.Test (Types.Header f,v))
        | (f,v)::x1 -> 
          loop x1 (fun pr -> Types.And(Types.Test(Types.Header f,v),pr)) in 
    loop x (fun x -> x)

  let set_to_netkat (xs:Set.t) : Types.pred =
    match Set.choose xs with 
      | None -> 
        Types.False
      | Some x -> 
        let xs' = Set.remove xs x in
        let f pol x = Types.Or(pol, to_netkat x) in
        Set.fold xs' ~init:(to_netkat x) ~f:f
end

module type ATOM = sig
  type t = Pattern.Set.t * Pattern.t
  module Set : Set.S with type Elt.t = t
  module Map : Map.S with type Key.t = t
  val to_string : t -> string
  val compare : t -> t -> int 
  val mk : Pattern.t -> t
  val tru : t
  val neg : t -> Set.t
end

module Atom : ATOM = struct

  type t = (Pattern.Set.t * Pattern.t) sexp_opaque with sexp

  let compare ((xs1,x1):t) ((xs2,x2):t) : int = 
    let cmp = Pattern.Set.compare xs1 xs2 in 
    if cmp <> 0 then cmp
    else Pattern.compare x1 x2  

  type this_t = t with sexp

  module Set = Set.Make(struct
    type t = this_t with sexp
    let compare = compare
  end)

  module Map = Map.Make(struct
    type t = this_t with sexp
    let compare = compare
  end)

  let to_string ((xs,x):t) : string = 
    Printf.sprintf "{%s},%s"
      (Pattern.set_to_string xs)
      (Pattern.to_string x)

  let mk (x:Pattern.t) : t =
    (Pattern.Set.empty, x)

  let tru : t = 
    mk Pattern.tru

  let check ((xs,x):t) : t option =
    Some (xs,x)
    
  let seq ((xs1,x1):t) ((xs2,x2):t) : t option =
    match Pattern.seq x1 x2 with
      | Some x12 ->
        check (Pattern.Set.union xs1 xs2, x12)
      | None ->
        None

  let neg (xs,x) : Set.t = 
    let init = 
      match check (Pattern.Set.singleton x, Pattern.tru) with 
        | None -> Set.empty
        | Some r -> Set.singleton r in 
    Pattern.Set.fold xs
      ~init:init
      ~f:(fun acc xi -> Set.add acc (mk xi))
end

module type LOCAL = sig
  type t 
  val to_string : t -> string
  val of_pred : Types.pred -> t
  val of_policy : Types.policy -> t
end 

module type OPTIMIZE = sig
  open Types 
  val mk_and : pred -> pred -> pred
  val mk_or : pred -> pred -> pred
  val mk_not : pred -> pred
  val mk_filter : pred -> policy
  val mk_mod : field -> fieldVal -> policy
  val mk_seq : policy -> policy -> policy
  val mk_par : policy -> policy -> policy
  val mk_star : policy -> policy
  val specialize_pred : fieldVal -> pred -> pred
  val specialize_policy : fieldVal -> policy -> policy
end

module Optimize : OPTIMIZE = struct
  let mk_and pr1 pr2 = 
    match pr1, pr2 with 
      | Types.True, _ -> 
        pr2
      | _, Types.True -> 
        pr1
      | Types.False, _ -> 
        Types.False
      | _, Types.False -> 
        Types.False
      | _ -> 
        Types.And(pr1, pr2)

  let mk_or pr1 pr2 = 
    match pr1, pr2 with 
      | Types.True, _ -> 
        Types.True
      | _, Types.True -> 
        Types.True
      | Types.False, _ -> 
        pr2
      | _, Types.False -> 
        pr2
      | _ -> 
        Types.Or(pr1, pr2)

  let mk_not pat =
    match pat with
      | Types.False -> Types.True
      | Types.True -> Types.False
      | _ -> Types.Neg(pat) 

  let mk_mod f v = 
    Types.Mod (Types.Header f,v)

  let mk_filter pr = 
    Types.Filter (pr)

  let mk_par pol1 pol2 = 
    match pol1, pol2 with
      | Types.Filter Types.False, _ -> 
        pol2
      | _, Types.Filter Types.False -> 
        pol1
      | _ -> 
        Types.Par(pol1,pol2) 

  let mk_seq pol1 pol2 =
    match pol1, pol2 with
      | Types.Filter Types.True, _ -> 
        pol2
      | _, Types.Filter Types.True -> 
        pol1
      | Types.Filter Types.False, _ -> 
        pol1
      | _, Types.Filter Types.False -> 
        pol2
      | _ -> 
        Types.Seq(pol1,pol2) 

  let mk_choice pol1 pol2 =
    match pol1, pol2 with
      | _ -> Types.Choice(pol1,pol2) 

  let mk_star pol = 
    match pol with 
      | Types.Filter Types.True -> 
        pol
      | Types.Filter Types.False -> 
        Types.Filter Types.True
      | Types.Star(pol1) -> pol
      | _ -> Types.Star(pol)
  
  let specialize_pred sw pr = 
    let rec loop pr k = 
      match pr with
        | Types.True ->
          k pr
        | Types.False ->
          k pr
        | Types.Neg pr1 ->
          loop pr1 (fun pr -> k (mk_not pr))
        | Types.Test (Types.Switch, v) ->
          if v = sw then 
            k Types.True
          else
            k Types.False
        | Types.Test (h, v) ->
          k pr
        | Types.And (pr1, pr2) ->
          loop pr1 (fun p1 -> loop pr2 (fun p2 -> k (mk_and p1 p2)))
        | Types.Or (pr1, pr2) ->
          loop pr1 (fun p1 -> loop pr2 (fun p2 -> k (mk_or p1 p2))) in 
    loop pr (fun x -> x)

  let specialize_policy sw pol = 
    let rec loop pol k = 
      match pol with  
        | Types.Filter pr ->
          k (Types.Filter (specialize_pred sw pr))
        | Types.Mod (h, v) ->
          k pol 
        | Types.Par (pol1, pol2) ->
          loop pol1 (fun p1 -> loop pol2 (fun p2 -> k (mk_par p1 p2)))
        | Types.Choice (pol1, pol2) ->
          loop pol1 (fun p1 -> loop pol2 (fun p2 -> k (mk_choice p1 p2)))
        | Types.Seq (pol1, pol2) ->
          loop pol1 (fun p1 -> loop pol2 (fun p2 -> k (mk_seq p1 p2)))
        | Types.Star pol ->
          loop pol (fun p -> k (mk_star p))
        | Types.Link(sw,pt,sw',pt') ->
	  failwith "Not a local policy" in 
    loop pol (fun x -> x) 
end

module Local : LOCAL = struct

  type t = Action.group Atom.Map.t * Atom.Set.t

  let to_string ((m,d):t) : string =
    Printf.sprintf "%s\n%s"
      (Atom.Map.fold m 
         ~init:""
         ~f:(fun ~key:r ~data:g acc ->
             Printf.sprintf "%s(%s) => %s\n"
               acc
               (Atom.to_string r) 
               (Action.group_to_string g)))
      (Atom.Set.fold d
         ~init:""
         ~f:(fun acc r -> 
               Printf.sprintf "%s%s%s"
                 acc
                 (Atom.to_string r)
                 (Action.group_to_string Action.group_drop)))

  let extend (r:Atom.t) (g:Action.group) ((m,d):t) : t =
    if Action.group_is_drop g then (m,Atom.Set.add d r) 
    else 
      if Atom.Map.mem m r then
        let msg = Printf.sprintf "Local.extend: overlap on atom %s" (Atom.to_string r) in 
        failwith msg
      else
        (Atom.Map.add m r g, d)

  let intersect (op:Action.group -> Action.group -> Action.group) (p:t) (q:t) : t = 
    failwith "NYI"

  let bin : t -> t -> t = 
    failwith "NYI"
      
  let par : t -> t -> t = 
    failwith "NYI"
      
  let choice : t -> t -> t = 
    failwith "NYI"

  let seq : t -> t -> t =
    failwith "NYI"

  let neg : t -> t = 
    failwith "NYI"

  let star : t -> t = 
    failwith "NYI"

  let rec of_pred (pr:Types.pred) : t =
    let rec loop pr k = 
      match pr with
      | Types.True ->
        let m = Atom.Map.singleton Atom.tru Action.group_id in 
        let d = Atom.Set.empty in 
        k (m,d)
      | Types.False ->
        let m = Atom.Map.empty in 
        let d = Atom.Set.singleton Atom.tru in 
        k (m,d)
      | Types.Neg pr ->
        loop pr (fun (p:t) -> k (neg p))
      | Types.Test (Types.Switch, v) ->
        failwith "Not a local policy"
      | Types.Test (Types.Header f, v) ->
        let x = Pattern.mk f v in  
        let r = Atom.mk x in 
        let m = Atom.Map.singleton r Action.group_id in 
        let d = Atom.neg r in 
        k (m,d) 
      | Types.And (pr1, pr2) ->
        loop pr1 (fun p1 -> loop pr2 (fun p2 -> k (seq p1 p2)))
      | Types.Or (pr1, pr2) ->
        loop pr1 (fun p1 -> loop pr2 (fun p2 -> k (par p1 p2))) in 
    loop pr (fun x -> x)

  let of_policy (pol:Types.policy) : t =
    let rec loop pol k =  
      match pol with
        | Types.Filter pr ->
          k (of_pred pr)
        | Types.Mod (Types.Switch, v) ->
          failwith "Not a local policy"
        | Types.Mod (Types.Header f, v) -> 
          let a = Action.mk f v in 
          let g = Action.group_mk (Action.Set.singleton a) in 
          let m = Atom.Map.singleton Atom.tru g in 
          let d = Atom.Set.empty in 
          k (m,d)
        | Types.Par (pol1, pol2) ->
          loop pol1 (fun p1 -> loop pol2 (fun p2 -> k (par p1 p2)))
        | Types.Choice (pol1, pol2) ->
          loop pol1 (fun p1 -> loop pol2 (fun p2 -> k (choice p1 p2)))
        | Types.Seq (pol1, pol2) ->
          loop pol1 (fun p1 -> loop pol2 (fun p2 -> k (seq p1 p2)))
        | Types.Star pol ->
          loop pol (fun p -> k (star p))
        | Types.Link(sw,pt,sw',pt') ->
	  failwith "Not a local policy" in 
    loop pol (fun p -> p)

  let to_netkat ((m,d):t) : Types.policy =
    let open Optimize in 
    let rec loop m =
    match Atom.Map.min_elt m with 
      | None -> 
        Types.Filter Types.False
      | Some (r,g) -> 
        let m' = Atom.Map.remove m r in
        let (xs,x) = r in
        let nc_pred = mk_and (mk_not (Pattern.set_to_netkat xs)) (Pattern.to_netkat x) in
        let nc_pred_acts = mk_seq (Types.Filter nc_pred) (Action.group_to_netkat g) in
        mk_par nc_pred_acts  (loop m') in
    loop m
end

(* exports *)
type t = unit
let of_policy = failwith "NYI"
let to_netkat = failwith "NYI" 
let compile = failwith "NYI" 
let decompile = failwith "NYI" 
let to_table = failwith "NYI"
