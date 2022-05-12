signature MULTISET =
sig
    type 'a multiset;
    val empty : 'a multiset;
    val is_empty : 'a multiset -> bool;
    val single : 'a -> 'a multiset;
    val append : 'a multiset -> 'a multiset -> 'a multiset;
    val cons : 'a -> 'a multiset -> 'a multiset;
    val collide : ('a -> 'a -> bool) -> 'a multiset -> 'a multiset -> 'a multiset;
    val map : ('a -> 'b) -> 'a multiset -> 'b multiset;
    val mapPartial : ('a -> 'b option) -> 'a multiset -> 'b multiset;
    val flatmap : ('a -> 'b multiset) -> 'a multiset -> 'b multiset;
    val filter : ('a -> bool) -> 'a multiset -> 'a multiset;
    val flat : 'a multiset multiset -> 'a multiset;
    val pick : ('a -> bool) -> 'a multiset -> 'a option * 'a multiset;
    val pick_option : ('a -> 'b option) -> 'a multiset -> 'b option * 'a multiset;
    val pick_map : ('a * 'a multiset -> 'b) -> 'a multiset -> 'b multiset;
    val eq : ('a -> 'a -> bool) -> 'a multiset -> 'a multiset -> bool;
    val fold : (('a * 'b) -> 'b) -> 'b -> 'a multiset -> 'b;
    val intersect : ('a -> 'a -> bool) -> 'a multiset -> 'a multiset -> 'a multiset;
    val union : ('a -> 'a -> bool) -> 'a multiset -> 'a multiset -> 'a multiset;
    val remove : ('a -> bool) -> 'a list -> 'a list;
    val subtract : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list;
    val count : ('a -> bool) -> 'a list -> int;
    val daisy_chain : 'a multiset -> ('a * 'a) multiset;
    val list_of : 'a multiset -> 'a list;
    val of_list : 'a list -> 'a multiset;
    val pairings : 'a multiset -> 'b multiset -> ('a * 'b) multiset multiset;
    val size : 'a multiset -> int;
    val all : ('a -> bool) -> 'a multiset -> bool;
    val cancel : ('a -> 'a -> bool) -> ('a multiset * 'a multiset) -> ('a multiset * 'a multiset);
end

structure Multiset : MULTISET =
struct
    type 'a multiset = 'a list;
    val empty = [];
    val is_empty = List.null;
    fun single x = [x];
    fun append x y = x @ y;
    fun cons x y = x :: y;
    val map = List.map;
    val mapPartial = List.mapPartial;
    val flatmap = List.flatmap;
    val filter = List.filter;
    fun flat [] = []
      | flat (x::xs) = x @ (flat xs);
    fun pick p [] = (NONE, [])
      | pick p (x::xs) = 
            if p x then
                (SOME(x),xs) 
            else
                let val (q,r) = pick p xs; in (q,x::r) end;
    
    fun pick_option p [] = (NONE, [])
      | pick_option p (x::xs) = 
                if is_some (p x) then
                    (p x,xs) 
                else
                    let val (q,r) = pick_option p xs; in (q,x::r) end;
    fun pick_map p xs =
        let fun f p [] _ = []
              | f p (y::ys) zs = p (y,zs@ys) :: f p ys (y::zs);
        in
            f p xs []
        end
    
    fun collide p [] ys = ys
      | collide p (x::xs) ys = (case pick (p x) ys of
            (NONE,_) => collide p xs (x::ys)
          | (SOME(y),nys) => collide p xs nys
      )
    
    val fold = List.foldr;
    fun count p [] = 0
      | count p (x::xs) = if p x then (count p xs) + 1 else count p xs;
    fun intersect eq [] l2 = []
      | intersect eq (x::xs) l2 = if count (eq x) xs < count (eq x) l2  then 
            x::(intersect eq xs l2) 
        else 
            intersect eq xs l2;
    fun remove p [] = []
        | remove p (y::ys) = if p y then ys else y::(remove p ys);
    fun subtract eq [] l2 = l2
        | subtract eq (x::xs) l2 = remove (eq x) (subtract eq xs l2);
    fun union eq x y = append x (subtract eq x y)
    fun eq ieq [] [] = true
      | eq ieq [] _ = false
      | eq ieq _ [] = false
      | eq ieq (x::xs) (ys) = (case pick (ieq x) ys of
            (NONE, _) => false
          | (SOME(z), zs) => eq ieq xs zs);
    
    fun daisy_chain [] = []
      | daisy_chain [_] = []
      | daisy_chain (x::(y::z)) = (x,y)::(daisy_chain (y::z));
    
    fun list_of x = x;
    fun of_list x = x;
    
    fun pairings [] _ = []
      | pairings (x::xs) ys = 
            let fun take_each [] acc =  []
                  | take_each (y::ys) acc =
                        (y, acc @ ys) :: take_each ys (y::acc);
            in
                List.flatmap (fn (z,zs) => List.map (fn w => (x,z)::w) (pairings xs zs)) (take_each ys [])
            end;

    fun cancel f (x,y) = let val intersection = intersect f x y in (subtract f intersection x, subtract f intersection y) end;

    val size = List.length;
    val all = List.all;
end

signature MULTISET_PAIR = 
sig
    type 'a multiset_pair;
    val empty : 'a multiset_pair;
    val numerator : 'a multiset_pair -> 'a Multiset.multiset;
    val denominator : 'a multiset_pair -> 'a Multiset.multiset;
    val from_multiset : 'a Multiset.multiset -> 'a multiset_pair;
    val from_multisets : ('a -> 'a -> bool) -> ('a Multiset.multiset * 'a Multiset.multiset) -> 'a multiset_pair;
    val invert : 'a multiset_pair -> 'a multiset_pair;
    val multiply : ('a -> 'a -> bool) -> 'a multiset_pair * 'a multiset_pair -> 'a multiset_pair;
    val divide : ('a -> 'a -> bool) -> 'a multiset_pair * 'a multiset_pair -> 'a multiset_pair;
    val cons : ('a -> 'a -> bool) -> 'a -> 'a multiset_pair -> 'a multiset_pair;
    val uncons : ('a -> 'a -> bool) -> 'a -> 'a multiset_pair -> 'a multiset_pair;
    val eq : ('a -> 'a -> bool) -> 'a multiset_pair -> 'a multiset_pair -> bool;
    val normalising_factor : ('a -> 'a -> bool) -> 'a multiset_pair list -> 'a multiset_pair;
end

structure MultisetPair : MULTISET_PAIR = 
struct
    type 'a multiset_pair = 'a Multiset.multiset * 'a Multiset.multiset;
    val empty : 'a multiset_pair = ([],[])
    fun is_empty (x,y) = Multiset.is_empty x andalso Multiset.is_empty y;
    fun numerator (x,_) = x;
    fun denominator (_,x) = x;
    fun from_multiset x = (x,[])
    val from_multisets = Multiset.cancel;
    fun invert ((x,y):'a multiset_pair) = (y,x);
    fun multiply p ((x1,y1):'a multiset_pair,(x2,y2):'a multiset_pair) = 
        let val (x1',y2') = Multiset.cancel p (x1,y2); 
            val (x2',y1') = Multiset.cancel p (x2,y1);
        in
            (x1'@x2',y1'@y2')
        end;
    fun cons p x (xs,ys) = case Multiset.pick (p x) ys of
            (NONE,_) => (x::xs,ys)
          | (SOME(z),zs) => (xs,zs);
    fun uncons p y (xs,ys) = case Multiset.pick (p y) xs of
            (NONE,_) => (xs,y::ys)
          | (SOME(z),zs) => (zs,ys);
    fun eq p x y = is_empty (multiply p (x,(invert y)));
    fun divide p ((x1,y1),(x2,y2)) = from_multisets p (Multiset.append x1 y2, Multiset.append y1 x2);
    fun normalising_factor p [] = empty
      | normalising_factor p (x::xs) = List.foldl (fn ((a,b),(c,d)) => (Multiset.intersect p a c, Multiset.union p b d)) x xs;
end