:: todo: PR into urbit master, and relink from
:: ../../garden-dev/lib/mip.hoon
|%
++  mip                                                 ::  map of maps
  |$  [kex key value]
  (map kex (map key value))
::
++  bi                                                  ::  mip engine
  =|  a=(mip)
  |@
  ++  del
    |*  [b=* c=*]
    =+  d=(~(gut by a) b ~)
    =+  e=(~(del by d) c)
    ?~  e
      (~(del by a) b)
    (~(put by a) b e)
  ::
  ++  get
    |*  [b=* c=*]
    =>  .(b `_?>(?=(^ a) p.n.a)`b, c `_?>(?=(^ a) ?>(?=(^ q.n.a) p.n.q.n.a))`c)
    ^-  (unit _?>(?=(^ a) ?>(?=(^ q.n.a) q.n.q.n.a)))
    (~(get by (~(gut by a) b ~)) c)
  ::
  ++  got
    |*  [b=* c=*]
    (need (get b c))
  ::
  ++  gut
    |*  [b=* c=* d=*]
    (~(gut by (~(gut by a) b ~)) c d)
  ::
  ++  has
    |*  [b=* c=*]
    !=(~ (get b c))
  ::
  ++  key
    |*  b=*
    ~(key by (~(gut by a) b ~))
  ::
  ++  put
    |*  [b=* c=* d=*]
    %+  ~(put by a)  b
    %.  [c d]
    %~  put  by
    (~(gut by a) b ~)
  ::
  ++  run
    |*  b=_=>(~ |=([* * *] +<+))
    %-  ~(run by a)
    |=  c=_?>(?=(^ a) n.a)
    %-  ~(run by q.c)
    |=  d=_?>(?=(^ a) ?>(?=(^ q.n.a) n.q.n.a))
    (b p.c p.d q.d)
  ::
  ++  rut
    |*  b=_=>(~ |=([* * *] +<+))
    %-  ~(rut by a)
    |=  c=_?>(?=(^ a) n.a)
    %-  ~(rut by q.c)
    |=  d=_?>(?=(^ a) ?>(?=(^ q.n.a) n.q.n.a))
    (b p.c p.d q.d)
  ::
  ++  rep
    |*  b=_=>(~ |=([* * *] +<+))
    %-  ~(rep by a)
    =<  .(+<+ +<+:b)
    |=  [c=_?>(?=(^ a) n.a) _+<+:b]
    =*  d  +<+
    %-  ~(rep by q.c)
    =<  .(+<+ d)
    |=  [e=_?>(?=(^ a) ?>(?=(^ q.n.a) n.q.n.a)) _+<+:b]
    =*  f  +<+
    (b [p.c p.e q.e] f)
  ::
  ++  rib
    |*  [b=* c=gate]
    ^+  [b a]
    %+  ~(rep by a)  b
    |=  [d=_?>(?=(^ a) n.a) b=_b]
    %+  ~(rep by q.d)  b
    |=  [e=_?>(?=(^ a) ?>(?=(^ q.n.a) n.q.n.a)) b=_b]
    (c [[p.d p.e] q.e] b)
  ::
  ++  tap
    ::NOTE  naive turn-based implementation find-errors ):
    =<  $
    =+  b=`_?>(?=(^ a) *(list [x=_p.n.a _?>(?=(^ q.n.a) [y=p v=q]:n.q.n.a)]))`~
    |.  ^+  b
    ?~  a
      b
    $(a r.a, b (welp (turn ~(tap by q.n.a) (lead p.n.a)) $(a l.a)))
  ::
  ++  uni
    |*  b=*
    ^+  a
    %-  %-  ~(uno by a)  b
    |*  $:  k=*
            w=*
            v=*
        ==
    =>  %=  .
          k  `_?>(?=(^ a) p.n.a)`k
          w  `_?>(?=(^ a) q.n.a)`w
          v  `_?>(?=(^ a) q.n.a)`v
        ==
    ^-  _?>(?=(^ a) q.n.a)
    (~(uni by w) v)
  ::
  --
  ::
--
