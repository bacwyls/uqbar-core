/-  *zink
/+  *zink-pedersen, *zink-json
/+  *mip
=>  |%
    +$  good      (unit *)
    +$  fail      (list [@ta *])
    +$  res       (each good fail)
    +$  body      (pair res hints)
    +$  appendix  [cax=cache =ax-map xi=@ud =arena ai=@ud bud=(unit @ud) scrys=(list *)]
    +$  book      (pair body appendix)
    --
|%
::
++  zebra                                                 ::  bounded zk +mule
  |=  [bud=(unit @ud) cax=cache scry=(unit granary-scry) [s=* f=*] test-mode=?]
  ^-  book
  %.  [s f test-mode]
  %*  .  zink
    app  [cax ~ 0 ~ 0 bud ?~(scry ~ [`*`u.scry ~])]
  ==
::
++  create-hints
  |=  [h=hints a=arena]
  ^-  json
  %-  pairs:enjs:format
  :~  nouns+(nouns:enjs a)
      hints+(hints:enjs h) 
  ==
::
++  zink
  =|  appendix
  =*  app  -
  =|  trace=fail
  |=  [s=* f=* test-mode=?]
  ^-  book
  =-  -(q.p q.p.-)
  |^  ^-  book
  =-  -(q ax-post(app q))
  |-  ^-  book
  =^  si  app  (index s)
  =^  fi  app  (index f)
  ?+    f
    ?@  f  [%|^trace [%invalid %&^f]~]^app
    ?>  ?=(@ -.f)
    [%|^trace [%invalid ~]~]^app
  ::
      [^ *]
    =^  [=hed=res =hed=hints]  app
      $(f -.f)
    ?:  ?=(%| -.hed-res)
      ~&  61  [%|^trace [%cons [si fi 0] hed-hints ~]~]^app
    ?~  p.hed-res  [%&^~ [%cons [si fi 0] hed-hints ~]~]^app
    =^  [=tal=res =tal=hints]  app
      $(f +.f)
    ?:  ?=(%| -.tal-res)
      ~&  65  [%|^trace [%cons [si fi 0] hed-hints tal-hints]~]^app
    ?~  p.tal-res  [%&^~ [%cons [si fi 0] hed-hints tal-hints]~]^app
    =/  prod  [u.p.hed-res u.p.tal-res]
    =^  pi  app  (index prod)
    [[%& `prod] [%cons [si fi pi] hed-hints tal-hints]~]^app
  ::
      [%0 axis=@]
    ?:  =(axis 0)  [%|^trace [%0 [si fi 0] 0]~]^app
    =^  tups  app  (frag axis.f s)
    :_  app
    [%& `n.tups]^[%0 [si fi ni.tups] ai.tups]~
  ::
      [%1 const=*]
    =^  pi  app  (index const.f)
    [[%& `const.f] [%1 [si fi pi]]~]^app
  ::
      [%2 sub=* for=*]
    =^  [=sub=res =sub=hints]  app
      $(f sub.f)
    ?:  ?=(%| -.sub-res)
      ~&  99  [%|^trace [%2 [si fi 0] sub-hints ~ ~]~]^app
    ?~  p.sub-res  [%&^~ [%2 [si fi 0] sub-hints ~ ~]~]^app
    =^  [=for=res =for=hints]  app
      $(f for.f)
    =/  hit=hints  [%2 [si fi 0] sub-hints for-hints ~]~
    ?:  ?=(%| -.for-res)
      ~&  103  [%|^trace hit]^app
    ?~  p.for-res  [%&^~ hit]^app
    =^  [=prod=res =prod=hints]  app
      $(s u.p.sub-res, f u.p.for-res)
    ?:  ?=(%| -.prod-res)  [%|^trace [%2 [si fi 0] sub-hints for-hints ~]~]^app
    ?~  p.prod-res  [prod-res [%2 [si fi 0] sub-hints for-hints ~]~]^app
    =^  pi  app  (index u.p.prod-res)
    [prod-res [%2 [si fi pi] sub-hints for-hints prod-hints]~]^app
  ::
      [%3 arg=*]
    :: TODO : out of gas errors
    ::        sf errors (sf itself errors or returns ~)
    =^  [=arg=res =arg=hints]  app
      $(f arg.f)
    ?:  ?=(%| -.arg-res)
      ~&  114  [%|^trace [%3 [si fi 0] ~]~]^app
    ?~  p.arg-res  [%&^~ [%3 [si fi 0] ~]~]^app
    ?@  u.p.arg-res
      =^  pi  app  (index %.n)
      :_  app
      :-  [%& ~ %.n]
      [%3 [si fi pi] arg-hints]~
    =^  pi  app  (index %.y)
    :_  app
    :-  [%& ~ %.y]
    [%3 [si fi pi] arg-hints]~
  ::
      [%4 arg=*]
    :: TODO : out of gas errors
    ::        proper sf errors
    ::        error if sf returns a cell, use the hash-req struct e.g. `%cell^[-.u.p.arg-res +.u.p.arg-res]]
    ::        error if sf returns ~ (this is here but not sure if it is correct)
    =^  [=arg=res =arg=hints]  app
      $(f arg.f)
    ?:  ?=(%| -.arg-res)
      ~&  131  [%|^trace [%4 [si fi 0] ~]~]^app
    ?~  p.arg-res  [%&^~ [%4 [si fi 0] arg-hints]~]^app
    ?^  u.p.arg-res
      ~&  135  [%|^trace [%4 [si fi 0] ~]~]^app
    =/  p  .+(u.p.arg-res)
    =^  pi  app  (index p)
    :_  app
    :-  [%& ~ p]
    [%4 [si fi pi] arg-hints]~
  ::
      [%5 a=* b=*]
    =^  [=a=res =a=hints]  app
      $(f a.f)
    ?:  ?=(%| -.a-res)
      ~&  146  [%|^trace [%5 [si fi 0] ~ ~]~]^app
    ?~  p.a-res  [%&^~ [%5 [si fi 0] ~ ~]~]^app
    =^  [=b=res =b=hints]  app
      $(f b.f)
    ?:  ?=(%| -.b-res)
      ~&  150  [%|^trace [%5 [si fi 0] a-hints b-hints]~]^app
    ?~  p.b-res  [%&^~ [%5 [si fi 0] a-hints b-hints]~]^app
    =/  p   =(u.p.a-res u.p.b-res)
    =^  pi  app  (index p)
    [[%& ~ =(u.p.a-res u.p.b-res)] [%5 [si fi pi] a-hints b-hints]~]^app
  ::
  ::  6 is special
  ::  if [subject test] returns anything but 0 1, fail
  ::  so we never have to hash yes/no in that case, hence 2
      [%6 test=* yes=* no=*]
    =^  [=t=res =t=hints]  app
      $(f test.f)
    ?:  ?=(%| -.t-res)
      ~&  164  [%|^trace [%6 [si fi 0] t-hints ~]~]^app
    ?~  p.t-res  [%&^~ [%6 [si fi 0] t-hints ~]~]^app
    =^  [=sf2=res =sf2=hints]  app
      ?+  u.p.t-res  `book`[%|^trace ~]^app
        %&  $(f yes.f)
        %|  $(f no.f)
      ==
    ?:  ?=(%| -.sf2-res)
      ~&  164  [%|^trace [%6 [si fi 0] sf2-hints ~]~]^app
    ?~  p.sf2-res  [%&^~ [%6 [si fi 0] sf2-hints ~]~]^app
    =^  pi  app  (index u.p.sf2-res)
    [[sf2-res [%6 [si fi pi] t-hints sf2-hints]~]]^app
  ::
      [%7 subj=* next=*]
    =^  [=sub=res =sub=hints]  app
      $(f subj.f)
    ?:  ?=(%| -.sub-res)  ~&  179  [%|^trace [%7 [si fi 0] sub-hints ~] ~]^app
    ?~  p.sub-res  [%&^~ [%7 [si fi 0] sub-hints ~] ~]^app
    =^  subi  app  (index u.p.sub-res)
    =^  [=nex=res =nex=hints]  app
      $(s u.p.sub-res, f next.f)
    ?~  p.nex-res  [nex-res [%7 [si fi 0] sub-hints nex-hints]~]^app
    ?:  =(%| -.nex-res)  [%|^trace [%7 [si fi 0] sub-hints ~]~]^app
    =^  pi  app  (index +>.nex-res)
    [nex-res [%7 [si fi pi] sub-hints nex-hints]~]^app
  ::
      [%8 hed=* next=*]
    =^  [=hed=res =hed=hints]  app
      $(f hed.f)
    =/  hit  [%8 [si fi 0] hed-hints ~]
    ?:  ?=(%| -.hed-res)  ~&  198  [%|^trace hit ~]^app
    ?~  p.hed-res  [%&^~ hit ~]^app
    =^  [=nex=res =nex=hints]  app
      $(s [u.p.hed-res s], f next.f)
    ?:  ?=(%| -.nex-res)  ~&  198  [%|^trace [%8 [si fi 0] hed-hints nex-hints] ~]^app
    ?~  p.nex-res  [%&^~ [%8 [si fi 0] hed-hints nex-hints]~]^app
    =^  pi  app  (index u.p.nex-res)
    [nex-res [%8 [si fi pi] hed-hints nex-hints]~]^app
  ::
      [%9 axis=@ core=*]
    ?:  =(axis 0)
      ~&  256  [%|^trace [%9 [si fi 0] ~ ~ 0 0]~]^app
    =^  [=core=res =core=hints]  app
      $(f core.f)
    ?:  ?=(%| -.core-res)
      ~&  211  [%|^trace [%9 [si fi 0] core-hints ~ 0 0]~]^app
    ?~  p.core-res  [%|^trace [%9 [si fi 0] core-hints ~ 0 0]~]^app
    =/  arm  (frag axis.f u.p.core-res)
    ::?:  ?=(%| -.p.arm)
    ::  ~&  269+[s axis.f]
    ::  :_  app
    ::  [%|^trace [%9 [si fi 0] core-hints ~ `@ud`axis.f q.arm]~]
    =^  [=res =res=hints]  app  $(s u.p.core-res, f n.arm)
    ?:  ?=(%| -.res)  [%|^trace [%9 [si fi 0] core-hints res-hints ni.arm ai.arm]~]^app
    ?~  p.res  [%&^~ [%9 [si fi 0] core-hints res-hints ni.arm ai.arm]~]^app
    =^  pi  app  (index u.p.res)
    [res [%9 [si fi pi] core-hints res-hints ni.arm ai.arm]~]^app
  ::
      [%10 [axis=@ value=*] target=*]
    !!
    :: ?:  =(0 axis.f)
    ::   ~&  232  [%|^trace [%10 [si fi 0] ~ ~ 0 ~]~]^app
    :: =^  [=val=res =val=hints]  app
    ::   $(f value.f)
    :: ?:  ?=(%| -.val-res)
    ::   ~&  239  [%|^trace [%10 [si fi 0] val-hints ~ 0 ~]~]^app
    :: ?~  p.val-res
    ::   [%&^~ [%10 [si fi 0] val-hints ~ 0 ~]~]^app
    :: =^  [=tar=res =tar=hints]  app
    ::   $(f target.f)
    :: ?:  ?=(%| -.tar-res)
    ::   ~&  235
    ::   :_  app
    ::   :-  %|^trace
    ::   [%10 [si fi 0] val-hints tar-hints 0 ~]~
    :: ?~  p.tar-res
    ::   :_  app
    ::   :-  %&^~
    ::   [%10 [si fi 0] val-hints tar-hints 0 ~]~
    :: =^  mutant  app
    ::   (edit axis.f u.p.tar-res u.p.val-res)
    :: =^  pi  app  (index mut.p.mutant)
    :: =^  ol  app  (index old.p.mutant)
    :: :_  app
    :: :-  %&^`mut.p.mutant
    :: :_  ~
    :: :*  %10  [si fi pi]  val-hints
    ::     tar-hints  ol  q.mutant
    :: ==
  ::
      [%11 tag=@ next=*]
    =^  itag  app  (index tag.f) 
    =^  [=next=res =next=hints]  app
      $(f next.f)
    ?:  ?=(%| -.next-res)  ~&  260  [%|^trace [%11 [si fi 0] next-hints %|^itag]~]^app
    ?~  p.next-res  [%&^~ [%11 [si fi 0] next-hints %|^itag]~]^app
    =/  p  .*(s [11 tag.f 1 u.p.next-res])
    =^  pi  app  (index p)
    :_  app
    [%&^`p [%11 [si fi pi] next-hints %|^itag]~]
  ::
      [%11 [tag=@ clue=*] next=*]
    ::  look for jet with this tag and compute sample
    ~&  >  "hint: {<`@tas`tag.f>}"
    ~?  ?=(%zfast tag.f)
      ?>  ?=([[%1 jet] *] clue.f) :: todo: shouldn't crash here
      =-  "jet: {(sa:dejs:format -)}"
      (en-jet:enjs ->.clue.f)
    =^  itag  app  (index tag.f)
    :: we can go straight to jetting in zere with this
    =^  [=clue=res =clue=hints]  app
      $(f clue.f)
    ?:  ?=(%| -.clue-res)
      ~&  269
      [%|^trace [%11 [si fi 0] ~ %&^[itag clue-hints]]~]^app
    ?~  p.clue-res  [%&^~ ~]^app
    ::  if jet exists for this tag, and sample is good,
    ::  replace execution with jet
    =^  [=next=res =next=hints]  app
      ?:  =(tag.f %zfast)
        :: todo: does this safe fail in zere? no it doesnt
        ?.  ?=([jet *] u.p.clue-res)
          [%|^trace [%11 [si fi 0] ~ %&^[itag clue-hints]]~]^app
        (run-jet +.clue.f u.p.clue-res)
      =?    trace
          ?=(?(%hunk %hand %lose %mean %spot) tag.f)
        [[tag.f u.p.clue-res] trace]
      $(f next.f) 
    ?:  ?=(%| -.next-res)
      ~&  190
      [%|^trace [%11 [si fi 0] ~ %&^[itag clue-hints]]~]^app
    ?~  p.next-res  [%&^~ [%11 [si fi 0] ~ %&^[itag clue-hints]]~]^app
    :_  app
    :_  [%11 [si fi 0] next-hints %&^[itag clue-hints]]~
    ?:  =(%fast tag.f)  %&^p.next-res
    :+  %&  ~
    .*  s
    [11 [tag.f 1 u.p.clue-res] 1 u.p.next-res]
  ::
  ==
  ::
  ++  index
    |=  [n=*]
    ^-  [^index appendix]
    =/  hit  (~(get by arena) n)
    ?^  hit  [q.u.hit app]
    ?@  n
      =/  ni  ai.app
      :-  ni
      app(arena (~(put by arena) n [atom+n ni]), ai +(ni))
    =^  hi  app  $(n -.n)
    =^  ti  app  $(n +.n)
    =/  ni  ai.app
    :-  ni
    app(arena (~(put by arena) n [cell+[hi ti] ni]), ai +(ni))
  ::
  ++  edit
    :: TODO you need to also include the edit along the path - i.e. [?(%2 %3) oldcellindex  newcellindex]
    |=  [axis=@ target=* value=*]
    ^-  [(pair [mut=* old=*] (list (trel ?(%2 %3) ^index ^index))) appendix]
    !!
    :: ?~  axis  !!
    :: =/  frg  (frag axis target)
    :: =/  mutant  .*(target [10 [axis 1 value] 0 1])
    :: =/  frgmut  (frag axis mutant)
    :: =/  efrg
    ::   %+  turn  (zip q.frg q.frgmut)
    ::   |=  [a=(pair ?(%2 %3) ^index) b=(pair ?(%2 %3) ^index)]
    ::   ^-  (trel ?(%2 %3) ^index ^index)
    ::   ?>  =(p.a p.b)
    ::   [p.a q.a q.b]
    :: [mutant^p.frg efrg]^app
  ::
  +$  rax-map  (mip ^index axis [rc=@ud p=^index path=(list ax-hint)])
  ++  ax-post
    |^
    =|  =rax-map
    =/  layer  ax-map
    |-  ^-  appendix
    ?:  =(~ layer)  app(ax-map (finalize rax-map))
    =-  $(ax-map ax-map, layer layer, rax-map rax-map, xi xi)
    %-  ~(rep by layer)
    |:  :*  [[s=*^index ax=*@ud] [*^index p=*^index path=*(list ax-hint)]]
            [ax-map=ax-map layer=`^ax-map`~ rax-map=rax-map xi=xi]
        ==
    ^-  [^^ax-map ^^ax-map ^^rax-map @ud]
    =/  sf  (sub-frag path rax-map)
    =-  [(~(uni by ax-map) layer) layer sf xi]
    %-  ~(rep bi sf)
    |:  :*  [s=*^index ax=*@ud [rc=*@ud p=*^index path=*(list ax-hint)]]
            [layer=layer xi=xi]
        ==
    ?:  (~(has by ax-map) s ax)  layer^xi
    ?.  (lth 0 rc)  layer^xi
    (~(put by layer) [s ax] xi p path)^[+(xi)]
    ::
    ++  reorder
      |=  =^ax-map
      |^
      %-  ~(rep by ax-map)
      |=  $:  [key=[s=^index ax=@ud] val=[xi=^index p=^index path=(list ax-hint)]]
              nax-map=^^ax-map
          ==
      %+  ~(put by nax-map)  key
      %_    val
          xi  (~(got by rexi) xi.val)
          path
        %+  turn  path.val
        |=  a=ax-hint
        ?.  ?=(%cache -.a)  a
        a(xi (~(got by rexi) xi.a))
      ::
      ==
      ::
      ++  rexi
        ~+  %-  tail
        %+  roll  sorted
        |=  [[^ [oxi=^index *]] [nxi=@ud m=(map ^index ^index)]]
        ~&  oxi+oxi
        ~&  nxi+nxi
        ~&  ax+[+<-<+]
        [+(nxi) (~(put by m) oxi nxi)]
      ::
      ++  sorted
        %+  sort  ~(tap by ax-map)
        |=  [[[* ax-a=@ud] *] [[* ax-b=@ud] *]]
        (lth ax-a ax-b)
      ::
      --
    ::
    ++  finalize
      |=  =rax-map
      =/  sorted  (sorted-rax rax-map)
      %-  reorder  %-  ~(rut by ax-map)
      |=  [[s=^index ax=@ud] [xi=^index p=^index path=(list ax-hint)]]
      =*  entry  +<+
      =|  out=(list ax-hint)
      ?:  ?=([[?(%2 %3) *] ~] path)  entry
      |-
      ?~  path  entry(path (flop out))
      ?:  =(1 ax)  entry(path (flop out))
      ?>  ?=(?(%2 %3) -.i.path)
      =/  step
        %-  head
        %+  skim  (~(gut by sorted) s ~)
        |=  [ax=@ud *]
        ?:  &(?=(?(%2 %3) ax) =(ax ^ax))  &
        =/  n  (dec (met 0 ax))
        ?.  (lth ax ^ax)  |
        .=  (cut 0 [0 n] (rsh [0 n] ^ax))
            (cut 0 [0 n] ax)
      %_    $
        s     p.step
        ax    (gep-b ax ax.step)
        path  (slag (dec (met 0 ax.step)) `(list ax-hint)`path)
        out   [[%cache s xi:(~(got by ax-map) s ax.step)] out]
      ==
    ::
    ++  gep-b
      |=  [c=axis a=axis]
      ?:  =(c a)  1
      =/  met-c  (met 0 c)
      =/  met-a  (met 0 a)
      =/  dif  (sub met-c met-a)
      =/  b-bits  (sub c (lsh [0 dif] a))
      (add b-bits (bex dif))
    ::
    ++  sorted-rax
      |=  =rax-map
      ~+  %-  ~(run by rax-map)
      |=  a=(map @ud [rc=@ud p=^index path=(list ax-hint)])
      ^-  (list [ax=@ud [rc=@ud p=^index path=(list ax-hint)]])
      %+  sort  (skim ~(tap by a) |=([ax=@ud [rc=@ud *]] (lth 1 rc)))
      |=  [[rc-a=@ud *] [rc-b=@ud *]]
      (lth rc-b rc-a)
    ::
    ++  sub-frag
      |=  [path=(list ax-hint) =rax-map]
      ^-  ^rax-map
      =-  (roll - [+(rax-map rax-map)]:[. peg-path])
      ^-  (list (list ax-hint))
      %-  zing
      %+  turn  (tails path)
      |=  path=(list ax-hint)
      ^-  (list (list ax-hint))
      (heads path)
    ::
    ++  peg-path
      |=  [path=(list ax-hint) =rax-map]
      ^-  ^rax-map
      ?~  path  !!
      ?>  ?=(?(%2 %3) -.i.path)
      =/  end  (head (flop `(list ax-hint)`path))
      ?>  ?=(?(%2 %3) -.end)
      =;  ax=@ud
        =/  rax  (~(gut bi rax-map) s.i.path ax [rc=0 p.end path])
        (~(put bi rax-map) s.i.path ax rax(rc +(rc.rax)))
      %+  roll  t.path
      |:  [step=*ax-hint lax=`@ud`-.i.path]
      ?>  ?=(?(%2 %3) -.step) :: todo: unnecessary, should always pass
      (peg lax -.step)
    ::
    ++  tails
      |=  path=(list ax-hint)
      ^-  (list (list ax-hint))
      |-
      ?~  path  ~
      :-  path
      $(path t.path)
    ::
    ++  heads
      |=  path=(list ax-hint)
      (turn (tails (flop path)) flop)
    ::
    --
  ::
  ++  frag
    |=  [axis=@ s=*]
    =/  start-axis  axis
    =/  start-s  s
    =^  is  app  (index s)
    |^  ^-  [[n=* ni=^index ai=^index] appendix] :: TODO add crash axis?
    =|  path=(list ax-hint)
    |-  ^-  [(trel * ^index ^index) appendix]
    =^  ip  app  (index s)
    ?:  =(1 axis)
      =?  .  !(~(has by ax-map) [is axis])
        .(xi +(xi), ax-map (~(put by ax-map) [is start-axis] [xi ip (flop path)]))
      [start-s ip p:(~(got by ax-map) [is start-axis])]^app
    ?~  axis  !!
    :: ?@  s  [%|^s^(gep-a start-axis axis) path]^app
    =/  pick  (cap axis)
    =/  child  ?-(pick %2 -.s, %3 +.s)
    =^  ic  app  (index child)
    %_  $
      s     child
      axis  (mas axis)
      path  [[pick ip ic] path]
    ==
    ::
    ::  solve for a in c = (peg a b)
    ++  gep-a
      |=  [p=@ b=@]
      =/  metb  (met 0 b)
      (rsh [0 (dec metb)] p)
    ::
    --
  ::
  ++  zip
    |*  [a=(list) b=(list)]
    ^-  (list _?>(?=(^ a) ?>(?=(^ b) [i.a i.b])))
    ?~  a  ~
    ?~  b  ~
    :-  [i.a i.b] 
    $(a t.a, b t.b)
  ::
  ++  hash
    |=  [n=*]
    |-  ^-  [phash appendix]
    ::  test mode disables hashing, so it won't generate valid hints.
    ::  however, computation is *much* faster since hashing is the
    ::  most expensive aspect of the process.
    ?:  test-mode  [0x1 app]
    |-  ^-  [phash appendix]
    =/  mh  (~(get by cax) n)
    ?^  mh
      [u.mh app]
    ?@  n
      =/  h  (hash:pedersen n 0)
      :-  h
      app(cax (~(put by cax) n h))
    =^  hh  app  $(n -.n)
    =^  ht  app  $(n +.n)
    =/  h  (hash:pedersen hh ht)
    :-  h
    app(cax (~(put by cax) n h))
  ::
  ++  zink-loop  $
  ::
  ++  take-bud
    |=  amt=@ud
    ^-  [? appendix]
    ?~  bud  %|^app
    ?:  (lth u.bud amt)  %&^app
    %|^app(u.bud (sub u.bud amt))
  ::
  ++  run-jet
    |=  [sam-clue=* =jet sam=*]
    ^-  book
    ?~  cost=(~(get by jets) jet)
      ~&  >>  "no jet found"  [%&^~ ~]^app
    ?:  ?&(?=(^ bud) (lth u.bud u.cost))  [%&^~ ~]^app
    ^-  book
    ?+    jet
      =-  [- [%jet jet (noun:enjs sam)]~]^app
      =^  oob  app  (take-bud u.cost)
      ?:  oob
        %&^~
      ?~  res=(run-zuse-jet jet sam-clue sam)  %|^trace
      %&^res
    ::
        [%$ %pedersen-hash]
      =^  oob  app  (take-bud u.cost)
      ?:  oob
        [%&^~ [%jet jet ~]~]^app
      ?.  ?=([@ @] sam)  [%|^trace ~]^app
      [%&^(some (hash:pedersen sam)) ~]^app
    ::
        [%$ %pmug]
      =^  hsam  app  (hash sam)
      [%&^~^hsam [%jet jet (noun:enjs sam)]~]^app
    ::
        [%$ %pgor]
      ?.  ?=([h=* t=*] sam)  [%|^trace ~]^app
      =/  hit  [%jet jet (noun:enjs sam)]~
      =^  res  app  (pgor sam)
      ?~  res  [%|^trace hit]^app
      [%&^res hit]^app
    ::
        [%$ %pmor]
      ?.  ?=([h=* t=*] sam)  [%|^trace ~]^app
      =/  hit  [%jet jet (noun:enjs sam)]~
      =^  res  app  (pmor sam)
      ?~  res  [%|^trace hit]^app
      [%&^res hit]^app
    ::
        [%$ %reel]
      ::  we want the hints in reverse order easier to
      ::  prove the list hash that way in zere
      ::  todo: oob early if not enough gas to hash list
      ?.  ?=([lis=* [bat=* [bunt-el=* acc=*] con=*]] sam)  [%|^trace ~]^app
      =^  hlis  app  (hash lis.sam)
      =^  hbat  app  (hash bat.sam)
      =^  hbunt-el  app  (hash bunt-el.sam)
      =^  hinit  app  (hash acc.sam)
      =^  hcon  app  (hash con.sam)
      |^
      =^  lax  app  (hash-and-flop lis.sam)
      ?.  ?=(%& -.lax)  [%|^trace [%jet jet (en-not-list p.lax)]~]^app
      =*  hax  p.p.lax
      =*  lis  q.p.lax
      =*  acc  acc.sam
      =|  hit=(list hints)
      |-  ^-  book
      ?~  lis  [%&^~^acc [%jet jet (en-hints hax (flop hit))]~]^app
      =^  [=el=res =el=hints]  app
        zink-loop(s [bat.sam [i.lis acc] con.sam], f bat.sam)
      =.  hit  el-hints^hit
      ?.  ?=(%& -.el-res)  [%|^trace [%jet jet (en-hints hax (flop hit))]~]^app
      ?~  p.el-res  [%&^~ [%jet jet (en-hints hax (flop hit))]~]^app
      $(acc u.p.el-res, lis t.lis)
      ::
      ++  en-hints
        |=  [hax=(list phash) hit=(list hints)]
        ^-  json
        %-  pairs:enjs:format
        :~  list+(num:enjs hlis)
            battery+(num:enjs hbat)
            bunt-el+(num:enjs hbunt-el)
            init+(num:enjs hinit)
            context+(num:enjs hcon)
            hashes+a+(turn hax num:enjs)
            hints+a+(turn hit hints:enjs)
        ==
      ::
      ++  en-not-list
        |=  [hax=(list phash) crash-end=@]
        ^-  json
        %-  pairs:enjs:format
        :~  list+(num:enjs hlis)
            battery+(num:enjs hbat)
            battery+(num:enjs hbat)
            bunt-el+(num:enjs hbunt-el)
            context+(num:enjs hcon)
            hashes+a+(turn hax num:enjs)
            crash-end+(num:enjs crash-end)
        ==
      ::
      --
    ::
        [%$ %roll]
      ::  we want the hints in reverse order easier to
      ::  prove the list hash that way in zere
      ::  todo: oob early if not enough gas to hash list
      ?.  ?=([lis=* [bat=* [bunt-el=* acc=*] con=*]] sam)  [%|^trace ~]^app
      =^  hlis  app  (hash lis.sam)
      =^  hbat  app  (hash bat.sam)
      =^  hbunt-el  app  (hash bunt-el.sam)
      =^  hinit  app  (hash acc.sam)
      =^  hcon  app  (hash con.sam)
      |^
      =^  lax  app  (hash-and-flop lis.sam)
      ?.  ?=(%& -.lax)  [%|^trace [%jet jet (en-not-list p.lax)]~]^app
      =*  hax  p.p.lax
      =*  lis  q.p.lax
      =*  acc  acc.sam
      =.  lis  (flop lis)  :: can probably make more efficient
      =|  hit=(list hints)
      |-  ^-  book
      ?~  lis  [%&^~^acc [%jet jet (en-hints hax (flop hit))]~]^app
      =^  [=el=res =el=hints]  app
        zink-loop(s [bat.sam [i.lis acc] con.sam], f bat.sam)
      =.  hit  el-hints^hit
      ?.  ?=(%& -.el-res)  [%|^trace [%jet jet (en-hints hax (flop hit))]~]^app
      ?~  p.el-res  [%&^~ [%jet jet (en-hints hax (flop hit))]~]^app
      $(acc u.p.el-res, lis t.lis)
      ::
      ++  en-hints
        |=  [hax=(list phash) hit=(list hints)]
        ^-  json
        %-  pairs:enjs:format
        :~  list+(num:enjs hlis)
            battery+(num:enjs hbat)
            bunt-el+(num:enjs hbunt-el)
            init+(num:enjs hinit)
            context+(num:enjs hcon)
            hashes+a+(turn hax num:enjs)
            hints+a+(turn hit hints:enjs)
        ==
      ::
      ++  en-not-list
        |=  [hax=(list phash) crash-end=@]
        ^-  json
        %-  pairs:enjs:format
        :~  list+(num:enjs hlis)
            battery+(num:enjs hbat)
            battery+(num:enjs hbat)
            bunt-el+(num:enjs hbunt-el)
            context+(num:enjs hcon)
            hashes+a+(turn hax num:enjs)
            crash-end+(num:enjs crash-end)
        ==
      ::
      --
    ::
        [%$ %turn]
      ::  we want the hints in reverse order easier to
      ::  prove the list hash that way in zere
      ::  todo: oob early if not enough gas to hash list
      ?.  ?=([lis=* [bat=* bunt=* con=*]] sam)  [%|^trace ~]^app
      =^  hlis  app  (hash lis.sam)
      =^  hbat  app  (hash bat.sam)
      =^  hbunt  app  (hash bunt.sam)
      =^  hcon  app  (hash con.sam)
      |^
      =^  lax  app  (hash-and-flop lis.sam)
      ?.  ?=(%& -.lax)  [%|^trace [%jet jet (en-not-list p.lax)]~]^app
      =*  hax  p.p.lax
      =*  lis  q.p.lax
      =|  hit=(list hints)
      =|  res=(list)
      |-  ^-  book
      ?~  lis  [%&^~^res [%jet jet (en-hints hax (flop hit))]~]^app
      =^  [=el=^res =el=hints]  app  zink-loop(s [bat.sam i.lis con.sam], f bat.sam)
      =.  hit  el-hints^hit
      ?.  ?=(%& -.el-res)  [%|^trace [%jet jet (en-hints hax (flop hit))]~]^app
      ?~  p.el-res  [%&^~ [%jet jet (en-hints hax (flop hit))]~]^app
      $(res u.p.el-res^res, lis t.lis)
      ::
      ++  en-hints
        |=  [hax=(list phash) hit=(list hints)]
        ^-  json
        %-  pairs:enjs:format
        :~  list+(num:enjs hlis)
            battery+(num:enjs hbat)
            bunt+(num:enjs hbunt)
            context+(num:enjs hcon)
            hashes+a+(turn hax num:enjs)
            hints+a+(turn hit hints:enjs)
        ==
      ::
      ++  en-not-list
        |=  [hax=(list phash) crash-end=@]
        ^-  json
        %-  pairs:enjs:format
        :~  list+(num:enjs hlis)
            battery+(num:enjs hbat)
            bunt+(num:enjs hbunt)
            context+(num:enjs hcon)
            hashes+a+(turn hax num:enjs)
            crash-end+(num:enjs crash-end)
        ==
      ::
      --
    ::
        [%$ %has %pin]
      ?~  sam=((soft ,[set=(tree) val=*]) sam)  [%|^trace ~]^app
      =>  .(sam u.sam)
      =^  [axis=@ leaf=(unit) path=(list phash)]  app
        (dig-in-tree set.sam val.sam same)
      =^  hset  app  (hash set.sam)
      =^  hval  app  (hash val.sam)
      =^  hleaf  app  (hash (fall leaf ~))
      =-  [%&^~^?~(leaf %| %&) hit]^app
      ^=  hit=(hints)
      :_  ~
      :+  %jet  jet
      %-  pairs:enjs:format
      :~  set+(num:enjs hset)
          val+(num:enjs hval)
          axis+(num:enjs axis)
          path+a+(turn path num:enjs)
          leaf+(num:enjs hleaf)
      ==
    ::
        [%$ %put %pin]
      ?~  sam=((soft ,[set=(tree) val=*]) sam)  [%|^trace ~]^app
      =>  .(sam u.sam)
      =^  res  app
        (put-in-tree set.sam val.sam same)
      =^  hset  app  (hash set.sam)
      =^  hval  app  (hash val.sam)
      ?.  ?=(%& +<.res)
        =-  [%&^~^a.res hit]^app
        ^=  hit=(hints)
        =/  [axis=@ path=(list phash)]  p.res
        :_  ~
        :+  %jet  jet
        %-  pairs:enjs:format
        :~  set+(num:enjs hset)
            val+(num:enjs hval)
            axis+(num:enjs axis)
            path+a+(turn path num:enjs)
        ==
      =-  [%&^~^a.res hit]^app
      ^=  hit=(hints)
      =/  [nodes=(list phash) left=(list phash) right=(list phash)]  p.res
      :_  ~
      :+  %jet  jet
      %-  pairs:enjs:format
      :~  set+(num:enjs hset)
          val+(num:enjs hval)
          nodes+a+(turn nodes num:enjs)
          left+a+(turn left num:enjs)
          right+a+(turn right num:enjs)
      ==
    ::
        [%tap %pin]
      ?~  set=((soft (tree)) sam)  [%|^trace ~]^app
      =>  .(set u.set)
      =^  hset  app  (hash set)
      =^  [res=(list) nodes=hash-tree]  app  (tap-in-tree set)
      =-  [%&^~^res hit]^app
      ^-  hit=hints
      :_  ~
      :+  %jet  jet
      %-  pairs:enjs:format
      :~  set+(num:enjs hset)
          nodes+(en-hash-tree nodes)
      ==
    ::
        [%apt %pin]
      ?~  set=((soft (tree)) sam)  [%|^trace ~]^app
      =>  .(set u.set)
      =^  hset  app  (hash set)
      =^  [res=? nodes=hash-tree]  app  (apt-in-tree set pgor pmor)
      =-  [%&^~^res hit]^app
      ^-  hit=hints
      :_  ~
      :+  %jet  jet
      %-  pairs:enjs:format
      :~  set+(num:enjs hset)
          nodes+(en-hash-tree nodes)
      ==
    ::  TODO : this is the exact same code as has. get rid of the duplication!
        [%$ %get %pby]
      ?~  sam=((soft ,[map=(tree) val=*]) sam)  [%|^trace ~]^app
      =>  .(sam u.sam)
      =^  [axis=@ leaf=(unit) path=(list phash)]  app
        ::  passing in val.sam as [val.sam ~] lets us use `head` everywhere - very clean!
        (dig-in-tree map.sam [val.sam ~] head)
      =^  [pkey=phash pval=phash ppkey=phash ppval=phash]  app
        (get-map-kvs map.sam axis)
      =^  hmap  app  (hash map.sam)
      =^  hval  app  (hash val.sam)
      =^  hleaf  app  (hash (fall leaf ~))
      =^  hlval  app  ?~  leaf
        [0 app]
      (hash +.u.leaf) :: do you need a `?>  =(^ u.leaf)` here?
      =-  [%&^~^?~(leaf %| %&) hit]^app
      ^=  hit=(hints)
      :_  ~
      :+  %jet  jet
      %-  pairs:enjs:format
      :~  map+(num:enjs hmap)
          val+(num:enjs hval)
          axis+(num:enjs axis)
          path+a+(turn path num:enjs)
          leaf+(num:enjs hleaf)
          leaf-val+(num:enjs hlval)
          p-key+(num:enjs pkey)
          p-val+(num:enjs pval)
          pp-key+(num:enjs ppkey)
          pp-val+(num:enjs ppval)
      ==
    ::
        [%$ %has %pby]
      ?~  sam=((soft ,[map=(tree) val=*]) sam)  [%|^trace ~]^app
      =>  .(sam u.sam)
      =^  [axis=@ leaf=(unit) path=(list phash)]  app
        ::  passing in val.sam as [val.sam ~] lets us use `head` everywhere - very clean!
        (dig-in-tree map.sam [val.sam ~] head)
      =^  [pkey=phash pval=phash ppkey=phash ppval=phash]  app
        (get-map-kvs map.sam axis)
      =^  hmap  app  (hash map.sam)
      =^  hval  app  (hash val.sam)
      =^  hleaf  app  (hash (fall leaf ~))
      =^  hlval  app  ?~  leaf
        [0 app]
      (hash +.u.leaf) :: do you need a `?>  =(^ u.leaf)` here?
      =-  [%&^~^?~(leaf %| %&) hit]^app
      ^=  hit=(hints)
      :_  ~
      :+  %jet  jet
      %-  pairs:enjs:format
      :~  map+(num:enjs hmap)
          val+(num:enjs hval)
          axis+(num:enjs axis)
          path+a+(turn path num:enjs)
          leaf+(num:enjs hleaf)
          leaf-val+(num:enjs hlval)
          p-key+(num:enjs pkey)
          p-val+(num:enjs pval)
          pp-key+(num:enjs ppkey)
          pp-val+(num:enjs ppval)
      ==
    ::
        [%$ %put %pby]
      ?~  sam=((soft ,[map=(tree) key=* val=*]) sam)  [%|^trace ~]^app
      =>  .(sam u.sam)
      =^  res  app
        (put-by-map map.sam [key.sam val.sam] head)
      =^  hmap  app  (hash map.sam)
      =^  hkey  app  (hash key.sam)
      =^  hval  app  (hash val.sam)
      ?.  ?=(%& +<.res)
        =-  [%&^~^a.res hit]^app
        ^=  hit=(hints)
        =/  [axis=@ old-node=phash path=(list phash)]  p.res
        :_  ~
        :+  %jet  jet
        %-  pairs:enjs:format
        :~  map+(num:enjs hmap)
            key+(num:enjs hkey)
            val+(num:enjs hval)
            axis+(num:enjs axis)
            old-node+(num:enjs old-node)
            path+a+(turn path num:enjs)
        ==
      =-  [%&^~^a.res hit]^app
      ^=  hit=(hints)
      =/  [keys=(list phash) vals=(list phash) left=(list phash) right=(list phash)]  p.res
      :_  ~
      :+  %jet  jet
      %-  pairs:enjs:format
      :~  map+(num:enjs hmap)
          key+(num:enjs hkey)
          val+(num:enjs hval)
          keys+a+(turn keys num:enjs)
          vals+a+(turn vals num:enjs)
          left+a+(turn left num:enjs)
          right+a+(turn right num:enjs)
      ==
    ::
        [%tap %pby] :: TODO this is *exactly* the same as tap:pin
      ?~  map=((soft (tree)) sam)  [%|^trace ~]^app
      =>  .(map u.map)
      =^  hmap  app  (hash map)
      =^  [res=(list) nodes=hash-tree]  app  (tap-in-tree map)
      =-  [%&^~^res hit]^app
      ^-  hit=hints
      :_  ~
      :+  %jet  jet
      %-  pairs:enjs:format
      :~  map+(num:enjs hmap)
          nodes+(en-hash-tree nodes)
      ==
    ::
        [%apt %pby]
      ?~  map=((soft (tree)) sam)  [%|^trace ~]^app
      =>  .(map u.map)
      =^  hmap  app  (hash map)
      =^  [res=? nodes=hash-map]  app  (apt-by-map map pgor pmor)
      =-  [%&^~^res hit]^app
      ^-  hit=hints
      :_  ~
      :+  %jet  jet
      %-  pairs:enjs:format
      :~  map+(num:enjs hmap)
          nodes+(en-hash-map nodes)
      ==
    ::
        [%$ %zock]
     ?.  ?=([bud=(unit @) [s=* f=*] scry=*] sam)  [%|^trace ~]^app
      =^  shash  app  (hash s.sam)
      =^  fhash  app  (hash f.sam)
      =^  hscry  app  (hash scry.sam)
      =/  inner-bud=(unit @ud)
        ?~  bud  bud.sam
        ?~  bud.sam  bud
        ?:  (lth u.bud u.bud.sam)  bud
        bud.sam
      =/  new-book
        %_    zink-loop
            s      s.sam
            f      f.sam
            scrys  scry.sam^scrys
            bud    inner-bud
        ==
      =/  diff
        ?~  inner-bud  0
        ?>  ?=(^ bud.q.new-book)
        (sub u.inner-bud u.bud.q.new-book)
      =/  outer-bud
        ?~  bud  bud
        `(sub u.bud diff)
      =/  real-inner-bud
        ?~  bud.sam  ~
        `(sub u.bud.sam diff)
      =/  =res
        ?-  p.p.new-book
            [%& ^]  %&^~^[%0 real-inner-bud u.p.p.p.new-book]
            [%& ~]
          ?:  =(outer-bud `0)  %&^~
          %&^~^[%1 real-inner-bud]
        ::
            [%| *]  %&^~^[%2 real-inner-bud]
        ==
      :-  res^[[%jet %$^%zock (noun:enjs [bud shash fhash hscry])] q.p.new-book]
      %_    app
          cax  cax.q.new-book
          bud  outer-bud
      ==
    ==
  ::
  +$  hash-tree  (tree [n=phash l=phash r=phash])
  +$  hash-map   (tree [n=[phash phash] l=phash r=phash]) :: TODO: is there an easy way to collapse hash-tree/map into one type? like an or?
  ++  en-hash-tree
    |=  =hash-tree
    |-  ^-  json
    ?~  hash-tree  ~
    %-  pairs:enjs:format
    :~  hn+(num:enjs n.n.hash-tree)
        hl+(num:enjs l.n.hash-tree)
        hr+(num:enjs r.n.hash-tree)
        l+$(hash-tree l.hash-tree)
        r+$(hash-tree r.hash-tree)
    ==
  ::
  ++  en-hash-map :: TODO : really similar to en-hash-tree. can you make them the same?
    |=  =hash-map
    |-  ^-  json
    ?~  hash-map  ~
    %-  pairs:enjs:format
    :~  hk+(num:enjs -.n.n.hash-map)
        hv+(num:enjs +.n.n.hash-map)
        hl+(num:enjs l.n.hash-map)
        hr+(num:enjs r.n.hash-map)
        l+$(hash-map l.hash-map)
        r+$(hash-map r.hash-map)
    ==
  ::
  ++  pgor
    |=  [a=* b=*]
    ^-  [(unit ?) appendix]
    =^  c  app  (hash a)
    =^  d  app  (hash b)
    ?:  =(c d)  ~^app
    [`(lth c d)]^app
  ::
  ++  pmor
    |=  [a=* b=*]
    ^-  [(unit ?) appendix]
    =^  c  app  (hash a)
    =^  d  app  (hash b)
    =^  c  app  (hash c)
    =^  d  app  (hash d)
    ?:  =(c d)  ~^app
    [`(lth c d)]^app
  ::
  ++  dig-in-tree :: basically dig, but returns axis in ~ case, and val
    |*  [a=(tree) b=* get=$-(* *)]
    ^-  [[axis=@ val=(unit _(get)) path=(list phash)] appendix]
    ?:  =(~ a)  [1 ~ ~]^app
    =/  axis  1
    =|  path=(list phash)
    |-  ^-  _^$
    ?~  a
      [axis ~ path]^app
    ?:  =((get b) (get n.a))
      =^  htala  app  (hash +.a)
      [(peg axis 2) `n.a htala^path]^app
    =^  hna  app  (hash n.a)
    =^  g  app  (pgor (get b) (get n.a))
    ?>  ?=(^ g)
    ?:  u.g
      =^  hra  app  (hash r.a)
      $(a l.a, axis (peg axis 6), path hra^hna^path)
    =^  hla  app  (hash l.a)
    $(a r.a, axis (peg axis 7), path hla^hna^path)
  ::
  ++  get-map-kvs
    |=  [map=(tree) axis=@]
    ^-  [[pkey=phash pval=phash ppkey=phash ppval=phash] appendix]
    ?~  (mod (xeb axis) 2)
      [~ ~ ~ ~]^app
    ?:  |(=(axis 6) =(axis 7))
      =^  pkey  app  (hash +4.map)
      =^  pval  app  (hash +5.map)
      [pkey pval ~ ~]^app
    =/  leaf-n-axis    (dec (div axis 2))
    =/  parent-n-axis  (dec (div axis 8))
    =^  pkey  app  (hash .*(map [0 (mul 2 leaf-n-axis)]))
    =^  pval  app  (hash .*(map [0 (succ (mul 2 leaf-n-axis))]))
    =^  ppkey  app  (hash .*(map [0 (mul 2 parent-n-axis)]))
    =^  ppval  app  (hash .*(map [0 (succ (mul 2 parent-n-axis))]))
    [pkey pval ppkey ppval]^app
  ::
  ++  put-in-tree
    |*  $:  a=(tree)  b=*
            get=$-(* *)
        ==
    =|  path=(list phash)
    =/  axis  1
    |-  ^-  $:  $:  a=_a
                    %+  each  [nodes=(list phash) left=(list phash) right=(list phash)]
                    [axis=@ path=(list phash)]
                ==
                appendix
            ==
    ?~  a
      [[b ~ ~] %& ~ ~ ~]^app
    ?:  =((get b) (get n.a))
      =^  htala  app  (hash +.a)
      [[b l.a r.a] %| (peg axis 2) htala^path]^app
    =^  hna  app  (hash n.a)
    =^  hra  app  (hash r.a)
    =^  hla  app  (hash l.a)
    =^  g  app  (pgor (get b) (get n.a))
    ?>  ?=(^ g)
    ?:  u.g
      =^  c  app  $(a l.a, path hra^hna^path, axis (peg axis 6))
      ?.  ?=(%& +<.c)  [c(a a(l a.c)) app]
      ?>  ?=(^ a.c)
      =^  m  app  (pmor (get n.a) (get n.a.c))
      ?>  ?=(^ m)
      :_  app
      %_  c
        nodes.p  hna^nodes.p.c
        left.p   hla^left.p.c
        right.p  hra^right.p.c
        a      ?:(u.m a(l a.c) a.c(r a(l r.a.c)))
      ==
    =^  c  app  $(a r.a, path hla^hna^path, axis (peg axis 7))
    ?.  ?=(%& +<.c)  [c(a a(r a.c)) app]
    ?>  ?=(^ a.c)
    =^  m  app  (pmor (get n.a) (get n.a.c))
    ?>  ?=(^ m)
    :_  app
    %_  c
      nodes.p  hna^nodes.p.c
      left.p   hla^left.p.c
      right.p  hra^right.p.c
      a        ?:(u.m a(r a.c) a.c(l a(r l.a.c)))
    ==
  ::
  ::  TODO this has a lot of shared logic with ++put-in-tree -> refactor later!
  ++  put-by-map
    |*  $:  a=(tree)  b=*
            get=$-(* *)
        ==
    =|  path=(list phash)
    =/  axis  1
    |-  ^-  $:  $:  a=_a
                    %+  each  [keys=(list phash) vals=(list phash) left=(list phash) right=(list phash)]
                    [axis=@ old-node=phash path=(list phash)]
                ==
                appendix
            ==
    ?~  a
      [[b ~ ~] %& ~ ~ ~ ~]^app
    ?:  =((get b) (get n.a))
      =^  htala  app  (hash +.a)
      =^  hold  app  (hash n.a)
      [[b l.a r.a] %| (peg axis 2) hold htala^path]^app
    =^  hna  app  (hash n.a)
    =^  hka  app  (hash -.n.a)
    =^  hva  app  (hash +.n.a)
    =^  hra  app  (hash r.a)
    =^  hla  app  (hash l.a)
    =^  g  app  (pgor (get b) (get n.a))
    ?>  ?=(^ g)
    ?:  u.g
      =^  c  app  $(a l.a, path hra^hna^path, axis (peg axis 6))
      ?.  ?=(%& +<.c)  [c(a a(l a.c)) app]
      ?>  ?=(^ a.c)
      =^  m  app  (pmor (get n.a) (get n.a.c))
      ?>  ?=(^ m)
      :_  app
      %_  c
        keys.p   hka^keys.p.c
        vals.p   hva^vals.p.c
        left.p   hla^left.p.c
        right.p  hra^right.p.c
        a      ?:(u.m a(l a.c) a.c(r a(l r.a.c)))
      ==
    =^  c  app  $(a r.a, path hla^hna^path, axis (peg axis 7))
    ?.  ?=(%& +<.c)  [c(a a(r a.c)) app]
    ?>  ?=(^ a.c)
    =^  m  app  (pmor (get n.a) (get n.a.c))
    ?>  ?=(^ m)
    :_  app
    %_  c
      keys.p   hka^keys.p.c
      vals.p   hva^vals.p.c
      left.p   hla^left.p.c
      right.p  hra^right.p.c
      a        ?:(u.m a(r a.c) a.c(l a(r l.a.c)))
    ==
  ::
  ++  tap-in-tree
    |=  a=(tree)
    ^-  [[res=(list) nodes=hash-tree] appendix]
    ?:  =(a ~)  [~ ~]^app
    =|  res=(list)
    |-  ^-  _^$
    ?~  a  [res ~]^app
    =^  hna  app  (hash n.a)
    =^  hla  app  (hash l.a)
    =^  hra  app  (hash r.a)
    =^  l  app  $(a l.a)
    =^  r  app  $(a r.a, res n.a^res.l)
    :_  app
    r(nodes [n=[hna hla hra] nodes.l nodes.r])
  ::
  ++  apt-in-tree
    |*  $:  a=(tree)
            gor=$-(^ [(unit ?) appendix])
            mor=$-(^ [(unit ?) appendix])
        ==
    ^-  [[? nodes=hash-tree] appendix]
    ?:  =(a ~)  [%& ~]^app
    =|  [l=(unit) r=(unit)]
    |-  ^-  $_  ^$
    ?~  a  [& ~]^app
    =^  hna  app  (hash n.a)
    =^  hla  app  (hash l.a)
    =^  hra  app  (hash r.a)
    =/  nodes  [hna hla hra]
    =^  g-na-ul   app  ?~(l [~ u=%&]^app (gor n.a u.l))
    ?>  ?=(^ g-na-ul)
    ?.  u.g-na-ul  [%| [nodes ~ ~]]^app
    =^  g-ur-na   app  ?~(r [~ u=%&]^app (gor u.r n.a))
    ?>  ?=(^ g-ur-na)
    ?.  u.g-ur-na  [%| [nodes ~ ~]]^app
    :: todo: prob more efficient to do mor first
    :: but zere jet is easier if not more efficient to write
    :: apt'ing l/r first
    =^  apt-la  app  $(a l.a, l `n.a)
    ?.  -.apt-la  [%| [nodes nodes.apt-la ~]]^app
    =^  apt-ra  app  $(a r.a, r `n.a)
    ?.  -.apt-ra  [%| [nodes nodes.apt-la nodes.apt-ra]]^app
    =^  m-na-nla  app  ?~(l.a [~ u=%&]^app (mor n.a n.l.a))
    ?>  ?=(^ m-na-nla)
    ?.  u.m-na-nla  [%| [nodes nodes.apt-la nodes.apt-ra]]^app
    =^  m-na-nra  app  ?~(r.a [~ u=%&]^app (mor n.a n.r.a))
    ?>  ?=(^ m-na-nra)
    ?.  u.m-na-nra  [%| [nodes nodes.apt-la nodes.apt-ra]]^app
    [%& [nodes nodes.apt-la nodes.apt-ra]]^app
  ::
  ++  apt-by-map :: TODO: almost exactly the same as apt-in-tree, could maybe solve it with a get=$-(* *), but return types are still different. Could make nodes=phash into (each phash [phash phash]) but idk
    |*  $:  a=(tree)
            gor=$-(^ [(unit ?) appendix])
            mor=$-(^ [(unit ?) appendix])
        ==
    ^-  [[? nodes=hash-map] appendix]
    ?:  =(a ~)  [%& ~]^app
    =|  [l=(unit) r=(unit)]
    |-  ^-  $_  ^$
    ?~  a  [& ~]^app
    =^  hka  app  (hash -.n.a) :: TODO why won't p.n.a work? type of a basically
    =^  hva  app  (hash +.n.a)
    =^  hla  app  (hash l.a)
    =^  hra  app  (hash r.a)
    =/  nodes  [[hka hva] hla hra]
    =^  g-na-ul   app  ?~(l [~ u=%&]^app (gor -.n.a -.u.l))
    ?>  ?=(^ g-na-ul)
    ?.  u.g-na-ul  [%| [nodes ~ ~]]^app
    =^  g-ur-na   app  ?~(r [~ u=%&]^app (gor -.u.r -.n.a))
    ?>  ?=(^ g-ur-na)
    ?.  u.g-ur-na  [%| [nodes ~ ~]]^app
    :: todo: prob more efficient to do mor first
    :: but zere jet is easier if not more efficient to write
    :: apt'ing l/r first
    =^  apt-la  app  $(a l.a, l `n.a)
    ?.  -.apt-la  [%| [nodes nodes.apt-la ~]]^app
    =^  apt-ra  app  $(a r.a, r `n.a)
    ?.  -.apt-ra  [%| [nodes nodes.apt-la nodes.apt-ra]]^app
    =^  m-na-nla  app  ?~(l.a [~ u=%&]^app (mor -.n.a -.n.l.a))
    ?>  ?=(^ m-na-nla)
    ?.  u.m-na-nla  [%| [nodes nodes.apt-la nodes.apt-ra]]^app
    =^  m-na-nra  app  ?~(r.a [~ u=%&]^app (mor -.n.a -.n.r.a))
    ?>  ?=(^ m-na-nra)
    ?.  u.m-na-nra  [%| [nodes nodes.apt-la nodes.apt-ra]]^app
    [%& [nodes nodes.apt-la nodes.apt-ra]]^app
  ::
  ++  hash-and-flop
    |=  [lis=*]
    =|  out=(list)
    =|  hax=(list phash)
    |-  ^-  [(each (pair (list phash) (list)) (pair (list phash) @)) appendix]
    ?~  lis  [%& hax out]^app
    ?@  lis  [%| hax lis]^app
    =^  hel  app  (hash -.lis)
    $(lis +.lis, out [-.lis out], hax [hel hax])
  ::
  ++  run-zuse-jet
    |=  [jet=* clue=* clue-res=*]
    ?>  ?=([@tas *] jet)
    =/  z=vase  !>(..zuse)
    =/  final-wing  -.jet
    =>  .(jet `*`+.jet)
    |^  ^-  (unit)
    =/  grabbed  (grab tail-wing)
    =/  ton
      (mink [q.z [7 q.grabbed (nock-10s-and-final p.grabbed)]] *$-(^ (unit (unit))))
    ?.(?=(%0 -.ton) ~ `product.ton)
    ::
    ++  final
      |=  =type
      q:(~(mint ut type) %noun [%wing [final-wing ~]])
    ::
    ++  nock-10s-and-final
      |=  =type
      |-  ^-  nock
      ?:  ?=([%0 axis=@] clue)
        [%7 [%10 [axis.clue %1 clue-res] %0 1] (final type)]
      ?>  ?=([i=[%0 axis=@] t=*] clue)
      ?>  ?=([i=* t=*] clue-res)
      :+    %7
        [%10 [axis.i.clue %1 i.clue-res] %0 1]
      $(clue t.clue, clue-res t.clue-res)
    ::
    ++  tail-wing
      =|  w=wing
      |-  ^-  wing
      ?@  jet  jet^w
      ?>  ?=([@ *] jet)
      $(jet `*`+.jet, w -.jet^w)
    ::
    ++  grab
      |=  wing=wing
      ^-  (pair type nock)
      =/  grab-form
        ?>  ?=(^ wing)
        %+  roll  t.wing
        |:  [limb=*limb hoon=`hoon`[%wing i.wing ~]]
        ^-  ^hoon
        [%tsgl [%wing limb ~] hoon]
      =/  z=vase  !>(..zuse)
      (~(mint ut p.z) %noun grab-form)
    --
  ::
  --
  ::
--
