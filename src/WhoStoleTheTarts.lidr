= Who Stole the Tarts?

\begin{code}
module WhoStoleTheTarts

%default total
\end{code}


== The First Tale

\begin{code}
namespace TheFirstTale
  %hide Prelude.Pairs.DPair.fst
\end{code}


=== Suspects

\begin{code}
  data MarchHare
  data MadHatter
  data Dormouse
\end{code}


=== Statements

\begin{quote}
I never stole the jam!
\end{quote}

\begin{code}
  MarchHareStatement : (truth : Bool) -> Type
  MarchHareStatement False = MarchHare
  MarchHareStatement True  = Not MarchHare
\end{code}

\begin{quote}
One of us stole it, but it wasn't me!
\end{quote}

\begin{code}
  HatterStatement : (truth : Bool) -> Type
  HatterStatement False = (Not MarchHare, Not Dormouse)
  HatterStatement True  = Either MarchHare Dormouse
  \end{code}

\begin{quote}
At least one of them [spoke the truth].
\end{quote}

\begin{code}
  DormouseStatement : (truth : Bool) -> Type
  DormouseStatement False = (MarchHareStatement False, HatterStatement False)
  DormouseStatement True  = Not (MarchHareStatement False, HatterStatement False)
\end{code}


=== Revelation

\begin{code}
  Revelation : Type
\end{code}

The March Hare and the Dormouse were not both speaking the truth, i.e.
either the March Hare spoke the truth and the Dormouse did not
\begin{code}
  Revelation = Either (MarchHareStatement True,  DormouseStatement False)
\end{code}

or the March Hare did not speak the truth and the Dormouse did.
\begin{code}
                      (MarchHareStatement False, DormouseStatement True)
\end{code}


=== Conclusion

The March Hare stole the jam.

\begin{code}
  Thief : MarchHareStatement _ -> HatterStatement _ -> DormouseStatement _
       -> Revelation
       -> Either MarchHare (Either MadHatter Dormouse)
  Thief _ _ _ rev  = Left (either (fst . snd) fst rev)
\end{code}
