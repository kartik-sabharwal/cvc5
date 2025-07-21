#lang scribble/base

@(require latex-utils/scribble/math latex-utils/scribble/utils)

@title[#:date ""]{Conflict Conjecture Generator}

@section{Synthesizing Conjectures with SyGuS}

Here are the broad strokes.
@itemlist[
#:style 'ordered
@item{@tt{candDeq} is populated with the equalities in the equivalence class of false.}

@item{The terms in @tt{candDeq} are `concretized' using the model values of the symbols they mention.}

@item{We use some approach, disregarding the exact details, to `expand' the equivalence classes of the candidate disequalities.}

@;We never substitute a function with its model value.
@;We never substitute in the model value for a symbol that appears in a universally quantified formula.
@;We always substitute in the model value if our variable is a skolem.
]

@section{Task}

Let's write a function that collects equalities in the equivalence class of false, concretizes them, and assigns a variable to each equivalence class that occurs in such an equality.

@section{Understanding @tt{checkDisequality()}}

@tt{checkDisequality()} starts by clearing the conjecture buffer but let's forget about that for now.

It takes a disequality @m{s = t} and produces variables for the representatives of @m{s} and @m{t}'s equivalence classes.

@section{Understanding @tt{getGeneralizationsInternal()}}

@(define lparen (elem "("))
@(define rparen (elem ")"))
@(define (surround elt) (list lparen elt rparen))
@(define (fvs elt) (list @elem[#:style "operatorname"]{fvs} (surround elt)))
@(define V @fvs{t})
@(define (var elt) @elem[elt #:style "mathit"])

The current environment maintains a bijection between some subset of the current equivalence class representatives and a set of variables.
Let's call each of these variables a @emph{representative variable}.

@tt{getGeneralizationsInternal()} essentially traverses a graph.
The nodes in this graph are terms that can be constructed using the available function symbols and the 
accepts a representative variable @m{v} as input.
This function tracks the 
It collects the known expansions of @m{v} in @m{@var{grecs}}.

@section{Understanding @tt{EMatchFrame}}

We have a class @tt{EMatchFrame}.
Given an equivalence class representative @m{r} and a pattern @m{m} it searches for terms @m{t} in the equivalence class of @m{r} for which there is a substitution @m{σ_t} such that @m{m σ_t} is entailed to be equal to @m{t}.
These are its fields.
@itemlist[
@item{
@tt{d_toMatch}.
The pattern against which we want to match.
}

@item{
@tt{d_matches}.  
For all @m{i ≥ @tt{d_index}} we have that @tt{d_matches[@m{i}]} is a term @m{t} in the equivalence class of @m{r} whose children agree with the corresponding ground children of @m{m}.  
We have not tried to perform matching on the rest of @m{m}'s children so far.
}

@item{
@tt{d_index}.  
The next index in @tt{d_matches} to consider.
}

@item{
@tt{d_recArgs}.
For each @m{i ∈ @tt{d_recArgs}}, @tt{m[@m{i}]} is a non-variable term that contains variables.
This means we'll have to analyze it recursively.
}

@item{
@tt{d_varArgs}.
For each @m{i ∈ @tt{d_varArgs}}, @tt{m[@m{i}]} is a variable.
}

@item{
@tt{d_varArgsBound}.
}
]
These are its methods.
@itemlist[
@item{@tt{push()}.  }
@item{@tt{pop()}.  }
@item{@tt{isFinished()}.  }
@item{@italic{Constructor}.  }
]
@; Here's the code for the class.
@; Let's attempt to describe its features in plain English.
@; @verbatim{
@; /**
@;  * The state of finding E-matches for a term in an equalivalence class
@;  */
@; class EMatchFrame
@; {
@;  public:
@;   EMatchFrame() {}
@;   /**
@;    * Initialize the list of terms in the equivalance class of r that may match
@;    * m.
@;    */
@;   EMatchFrame(TermDb* tdb, eq::EqualityEngine* ee, const Node& m, const Node& r)
@;       : d_toMatch(m), d_index(0)
@;   {
@;     Assert(ee->hasTerm(r) && ee->getRepresentative(r) == r && r.isConst());
@;     Node op = m.getOperator();
@;     // maps argument positions to the ground term representative of that
@;     // argument, for the ground arguments of m.
@;     std::map<size_t, Node> groundArgs;
@;     for (size_t i = 0, nargs = m.getNumChildren(); i < nargs; i++)
@;     {
@;       if (m[i].getKind() == Kind::BOUND_VARIABLE)
@;       {
@;         d_varArgs.push_back(i);
@;       }
@;       else if (!expr::hasBoundVar(m[i]))
@;       {
@;         Assert(ee->hasTerm(m[i]));
@;         groundArgs[i] = ee->getRepresentative(m[i]);
@;       }
@;       else
@;       {
@;         d_recArgs.push_back(i);
@;       }
@;     }
@;     // get the candidate terms in this equivalence class
@;     eq::EqClassIterator eqc = eq::EqClassIterator(r, ee);
@;     while (!eqc.isFinished())
@;     {
@;       Node n = *eqc;
@;       ++eqc;
@;       // must have the same operator, and be "active". The latter restriction
@;       // will filter terms that are congruent to another term we already
@;       // considered.
@;       if (!n.hasOperator() || n.getOperator() != m.getOperator()
@;           || !tdb->isTermActive(n))
@;       {
@;         continue;
@;       }
@;       Assert(n.getNumChildren() == m.getNumChildren());
@;       // prune ground disequal
@;       bool success = true;
@;       for (std::pair<const size_t, Node>& g : groundArgs)
@;       {
@;         Assert(g.first < n.getNumChildren());
@;         Assert(ee->hasTerm(n[g.first]));
@;         Node gr = ee->getRepresentative(n[g.first]);
@;         if (gr != g.second)
@;         {
@;           success = false;
@;           break;
@;         }
@;       }
@;       if (success)
@;       {
@;         d_matches.push_back(n);
@;       }
@;     }
@;   }
@;   /** The term we are matching */
@;   Node d_toMatch;
@;   /** The candidate list of terms */
@;   std::vector<Node> d_matches;
@;   /** The next index in d_matches to consider */
@;   size_t d_index;
@;   /** The argument positions of d_toMatch which are non-ground, non-variable */
@;   std::vector<size_t> d_recArgs;
@;   /** The argument positions of d_toMatch which are variables */
@;   std::vector<size_t> d_varArgs;
@;   /**
@;    * The set of variables we bound in the last successful call to push, if any.
@;    */
@;   std::unordered_set<size_t> d_varArgsBound;
@;   /**
@;    * Update match/emf based on matching the next term in the list of candidate
@;    * terms computed in the constructor of this class. This adds
@;    * - substitutions to match based on binding the direct variables of d_toMatch
@;    * - a list of obligations to match recursively to emf based on the
@;    * non-ground, non-variable chidlren of d_toMatch.
@;    *
@;    * return true if we successfully pushed to match/emf.
@;    */
@;   bool push(TermDb* tdb,
@;             eq::EqualityEngine* ee,
@;             Subs& match,
@;             std::vector<std::shared_ptr<EMatchFrame>>& emf)
@;   {
@;     Trace("cconj-em-debug") << "push " << std::endl;
@;     if (isFinished())
@;     {
@;       Trace("cconj-em-debug") << "...already finished" << std::endl;
@;       return false;
@;     }
@;     Node nextMatch = d_matches[d_index];
@;     d_index++;
@;     Assert(nextMatch.getNumChildren() == d_toMatch.getNumChildren());
@;     std::vector<Node> groundRec;
@;     for (size_t i : d_recArgs)
@;     {
@;       Assert(i < nextMatch.getNumChildren());
@;       Assert(ee->hasTerm(nextMatch[i]));
@;       Node r = ee->getRepresentative(nextMatch[i]);
@;       if (!r.isConst())
@;       {
@;         // non-constant
@;         Trace("cconj-em-debug") << "...non-const" << std::endl;
@;         return false;
@;       }
@;       groundRec.emplace_back(r);
@;     }
@;     Trace("cconj-em-debug") << "look at var args" << std::endl;
@;     // match the current vars
@;     for (size_t i : d_varArgs)
@;     {
@;       const Node& v = d_toMatch[i];
@;       Assert(v.getKind() == Kind::BOUND_VARIABLE);
@;       Node cur = match.getSubs(v);
@;       if (cur.isNull())
@;       {
@;         d_varArgsBound.insert(i);
@;         match.add(v, nextMatch[i]);
@;         continue;
@;       }
@;       Assert(ee->hasTerm(nextMatch[i]));
@;       if (!ee->areEqual(nextMatch[i], cur))
@;       {
@;         // failed a bound argument argument
@;         pop(match);
@;         Trace("cconj-em-debug") << "...bound conflict" << std::endl;
@;         return false;
@;       }
@;     }
@;     Trace("cconj-em-debug") << "push" << std::endl;
@;     Assert(groundRec.size() == d_recArgs.size());
@;     for (size_t i = 0, ngr = groundRec.size(); i < ngr; i++)
@;     {
@;       emf.emplace_back(std::make_shared<EMatchFrame>(
@;           tdb, ee, d_toMatch[d_recArgs[i]], groundRec[i]));
@;     }
@;     Trace("cconj-em-debug") << "...return success" << std::endl;
@;     return true;
@;   }
@;   /**
@;    * Pop, which cleans up match based on what was bound by this class in the
@;    * last successful call to push.
@;    */
@;   void pop(Subs& match)
@;   {
@;     for (size_t i : d_varArgsBound)
@;     {
@;       match.erase(d_toMatch[i]);
@;     }
@;     d_varArgsBound.clear();
@;   }
@;   bool isFinished() const { return d_index == d_matches.size(); }
@; };
@; }