The First Tale
==============

```idris
module WhoStoleTheTarts.TheFirstTale

%access  export
%default total

%hide Prelude.Pairs.DPair.fst
```

Someone stole the jam. Our job is to figure out who the thief was.

Suspects
--------

We know it was one of the

-   March Hare,

```idris
data MarchHare
```

-   Mad Hatter, or

```idris
data MadHatter
```

-   Dormouse

```idris
data Dormouse
```

... and that they worked alone.

```idris
SomeoneStoleTheJam : Type
SomeoneStoleTheJam = Either (    MarchHare, Not MadHatter, Not Dormouse)
                   $ Either (Not MarchHare,     MadHatter, Not Dormouse)
                            (Not MarchHare, Not MadHatter,     Dormouse)
```

Statements
----------

The March Hare claims,
<blockquote>
I never stole the jam!
</blockquote>

```idris
MarchHareStatement : (truth : Bool) -> Type
MarchHareStatement False =     MarchHare
MarchHareStatement True  = Not MarchHare
```

According to the Mad Hatter,
<blockquote>
One of us stole it, but it wasn't me!
</blockquote>

```idris
MadHatterStatement : (truth : Bool) -> Type
MadHatterStatement False = (    MadHatter, Not    MarchHare, Not Dormouse)
MadHatterStatement True  = (Not MadHatter, Either MarchHare      Dormouse)
```

As per the Dormouse,
<blockquote>
At least one of them (spoke the truth).
</blockquote>

```idris
DormouseStatement : (truth : Bool) -> Type
DormouseStatement False =     (MarchHareStatement False, MadHatterStatement False)
DormouseStatement True  = Not (MarchHareStatement False, MadHatterStatement False)
```

Revelation
----------

We're also given a revelation:

```idris
Revelation : Type
```

The March Hare and the Dormouse were not both speaking the truth, i.e. either

-   ... the March Hare spoke the truth and the Dormouse did not

```idris
Revelation = Either (MarchHareStatement True,  DormouseStatement False)
```

-   ... or the March Hare did not speak the truth and the Dormouse did.

```idris
                    (MarchHareStatement False, DormouseStatement True)
```

Conclusion
----------

Given the [statements](#statements) above and the [revelation](#revelation),

```idris
Thief : SomeoneStoleTheJam -> Revelation
```

... we can conclude the March Hare stole the jam.

```idris
     -> (MarchHare, Not MadHatter, Not Dormouse)
```

The first clause is a simple pattern match.

```idris
Thief (Left  marchHare)         _                        = marchHare
```

From the revelation, it follows that if the March Hare spoke the truth,
then the Dormouse lied. If the March Hare spoke the truth, then they
didn't steal the jam. But if the Dormouse lied, then so did the March Hare
and is guilty BWOC.

```idris
Thief _                         (Left  (itWas,(them,_))) = absurd (itWas them)
```

If the March Hare lied, then they stole the jam.

```idris
Thief (Left  (_,did,it))        (Right (marchHare,_))    = (marchHare,did,it)
```

If we assume the Mad Hatter stole jam and the March Hare lied,
then the March Hare did it BWOC.

```idris
Thief (Right (Left  (itWas,_))) (Right (them,_))         = absurd (itWas them)
```

Assume the Dormouse did it and lied. If the Dormouse lied,
then the March Hare lied, and therefore stole the jam.

```idris
Thief (Right (Right (itWas,_))) (Left  (_,(them,_)))     = absurd (itWas them)
```

Assume the Dormouse did it and the March Hare lied.
If the March Hare lied then they are guilty.

```idris
Thief (Right (Right (itWas,_))) (Right (them,_))         = absurd (itWas them)
```

∎
