/+  tiny
|%
++  epoch-interval    ~s10
::
+$  epoch   [num=@ud =start=time order=(list ship) =slots]
::
+$  epochs  ((mop @ud epoch) gth)
++  poc     ((on @ud epoch) gth)
::
+$  block         (pair signature chunks)
+$  block-header  [num=@ud prev-header-hash=@uvH data-hash=@uvH]
+$  slot          (pair block-header (unit block))
::
+$  slots  ((mop @ud slot) gth)
++  sot    ((on @ud slot) gth)
::
+$  signature  [p=@ux q=ship r=life]
+$  chunks     (set @)
+$  chunk      [=helix-id [(list [hash=@ux =call:tiny]) town:tiny]]
::
+$  helix-id  @ux
+$  helices  (map helix-id helix)
+$  helix
  $:  id=helix-id
      state=town:tiny
      order=(list ship)
      leader=ship
      num=@ud
  ==
::
+$  mempools  (map helix-id mempool)
+$  mempool   (set call:tiny)
::
+$  update
  $%  [%epochs-catchup =epochs]
      [%blocks-catchup epoch-num=@ud =slots]
      [%new-block epoch-num=@ud header=block-header =block]
      :: todo: add data availability data
      ::
      [%saw-block epoch-num=@ud header=block-header]
  ==
::
+$  action
  $%  [%start mode=?(%fisherman %validator) history=epochs validators=(set ship)]
      [%stop ~]
      [%new-epoch ~]
      ::  who gets to form a new helix? vote/sigs from the existing relay set?
      ::  what helices are hard-coded into the relay chain?
      ::  [%new-helix validators=(set ship)]
  ==
::
+$  mempool-action
  $%  [%receive =helix-id tx=call:tiny]
      [%hear =helix-id tx=call:tiny]
      [%forward-set =helix-id to=ship txs=(set call:tiny)]
      [%receive-set =helix-id txs=(set call:tiny)]
  ==
::
+$  chunk-action
  $%  [%hear =chunk]
      [%signed =helix-id =signature hash=@ux]
      [%submit sigs=(set signature) =chunk]
  ==
--
