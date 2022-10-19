/-  *zink
|%
++  enjs
  |%
  ++  nouns
    |=  c=arena
    ^-  json
    :-  %a
    %+  turn
    %+  sort  (turn ~(tap by c) tail)
    |=  [a=(pair tnoun index) b=(pair tnoun index)]
    (lth q.a q.b)
    en-noun
  ::
  ++  en-noun
    |=  n=(pair tnoun index)
    ^-  json
    =,  enjs:format
    ?-  -.p.n
        %atom
      (pairs atom+(num p.p.n) i+(num q.n) ~)
        %cell
      %-  pairs 
      :~  cell+a+~[(num p.p.n) (num q.p.n)]
          :: i+(num q.n)
      ==
    ==
  ::
  ++  hints
    |=  h=^hints
    ^-  json
    :: TODO: no list of hints
    ?>  ?=([* ~] h)
    (en-hint i.h)
  ::
  ++  en-hint
    |=  hin=cairo-hint
    ^-  json
    =,  enjs:format
    :: ?:  &(?=(_-:*$<(?(%1 %cons %invalid %jet) cairo-hint) -.hin) ?=(%| +<.hin))
    ::    (frond %broke (num p.hin))
    ::  for some reason previous conditional doesn't assert %& case here
    ::  it should mint-vain, but doesn't
    ?+  hin  !!
        [%0 * *]
      %-  pairs
      :~  'jmp_dest'^(num 0)
          pred+(en-pred pred.hin)
          :: path+(en-path path.hin)
      ==
        [%1 *]  (pairs 'jmp_dest'^(num 1) pred+(en-pred +.hin) ~)
    ::
        [%2 * * * *]
      %-  pairs
      :~  'jmp_dest'^(num 2)
          pred+(en-pred pred.hin)
          sf1+(hints sf1.hin)
          sf2+(hints sf2.hin)
          sf3+(hints sf3.hin)
      ==
    ::     
        [?(%3 %4) * *]
      %-  pairs
      :~  'jmp_dest'^(num -.hin)
          pred+(en-pred pred.hin)
          sf+(hints sf.hin)
      ==
    ::
        [?(%5 %6 %7 %8) * * *]
      %-  pairs
      :~  'jmp_dest'^(num -.hin)
          pred+(en-pred pred.hin)
          sf1+(hints sf1.hin)
          sf2+(hints sf2.hin)
      ==
    ::
        [%9 * * * *]
      %-  pairs
      :~  'jmp_dest'^(num 9)
          pred+(en-pred pred.hin)
          sf1+(hints sf1.hin)
          sf2+(hints sf2.hin)
          leaf+(num leaf.hin)
          :: path+(en-path path.hin)
      ==
    ::
        [%10 * * * * *]
      %-  pairs
      :~  'jmp_dest'^(num 10)
          pred+(en-pred pred.hin)
          sf1+(hints sf1.hin)
          sf2+(hints sf2.hin)
          oldleaf+(num old-leaf.hin)
          :: path+(en-path-10 path.hin)
      ==
    ::
        [%11 * * %| @]
      %-  pairs
      :~  'jmp_dest'^(num 11)
          pred+(en-pred pred.hin)
          sf+(hints sf.hin)
          tag+(num +>+>:hin)
      ==
    ::
        [%11 * * %& *]
      %-  pairs
      :~  pred+(en-pred pred.hin)
          sf+(hints sf.hin)
          tag+(num +>+>-:hin)
          clue+(hints +>+>+:hin)
      ==
    ::
        [%cons *]
      %-  pairs
      :~  'jmp_dest'^s+%cons
          pred+(en-pred pred.hin)
          sf1+(hints sf1.hin)
          sf2+(hints sf2.hin)
      ==   
 
    ==
    ::
  ++  en-jet
    |=  n=*
    ^-  json
    :-  %s
    |-  ^-  cord
    ?@  n  ?~(n '' (scot %tas n))
    ?>  ?=(@ -.n)
    ?~  -.n  $(n +.n)
    :((cury cat 3) (scot %tas -.n) ':' $(n +.n))
  ::
  ++  noun
    |=  n=*
    |-  ^-  json
    ?@  n  (num n)
    a+[$(n -.n) $(n +.n) ~]
  ::
  ++  en-11
    |=  [=pred sf=^hints a=(each [tag=@ clue=^hints] @)]
    ^-  json
    =,  enjs:format
    ?-  -.a
      %&  (pairs pred+(en-pred pred) tag+(num tag.p.a) clue+(hints clue.p.a) sf+(hints sf) ~)
      %|  (pairs pred+(en-pred pred) tag+(num p.a) sf+(hints sf) ~)
    ==
  ::
  ++  en-invalid
    |=  hin=(each @ [@ phash])
    ^-  json
    =,  enjs:format
    ?-  -.hin
      %&  (pairs is-atom+b+%& head+(num p.hin) ~)
      %|  (pairs is-atom+b+%| head+(num -.p.hin) tail+(num +.p.hin) ~)
    ==
  ::
  :: ++  en-subf
  ::   |=  subf
  ::   ^-  json
  ::   =,  enjs:format
  ::   (pairs hash+(num h) hints+(hints hit) ~)
  ::
  :: ++  en-hash-req
  ::   |=  hash-req
  ::   ^-  json
  ::   =,  enjs:format
  ::   ?-  +<-
  ::     %cell  (pairs head+(num head) tail+(num tail) ~)
  ::     %atom  (frond %atom (num val))
  ::   ==
  ::
  ++  en-leaf-or-atom
    |=  hin=(each phash [=atom crash-axis=@])
    ^-  json
    =,  enjs:format
    =,  p.hin
    ?-  -.hin
      %&  (frond %leaf (num p.hin))
      %|  (pairs atom+(num atom) crash-axis+(num crash-axis) ~)
    ==
  ::
  ++  en-path
    |=  path=(list (pair ?(%2 %3) index))
    a+(turn path en-path-elem)
  ::
  ++  en-path-elem
    |=  a=(pair @ud index)
    ^-  json
    =,  enjs:format
    a+[(num p.a) (num q.a) ~]
  ::
  ::  todo: less dumb
  ++  en-path-10
    |=  path=(list (trel ?(%2 %3) index index))
    a+(turn path en-path-elem-10)
  ::
  ++  en-path-elem-10
    |=  a=(trel ?(%2 %3) index index)
    ^-  json
    =,  enjs:format
    a+[(num p.a) (num q.a) (num r.a) ~]
 
  ::
  ++  en-pred
    |=  =pred
    ^-  json
    a+[(num s.pred) (num f.pred) (num p.pred) ~]
  ::
  ++  num
    |=  n=@ud
    ^-  json
    [%s `cord`(rsh [3 2] (scot %ui n))]
  --
--
