# Allen relations + filter
_accessibles(fr::Full1DFrame, w::Interval{Int}, r::FilteredRelation{_IA_A,IntervalLengthFilter{≤}}) = zip(Iterators.repeated(w.y), w.y+1+(r.wf.k):X(fr)+1)
_accessibles(fr::Full1DFrame, w::Interval{Int}, r::FilteredRelation{_IA_A,IntervalLengthFilter{≥}}) = zip(Iterators.repeated(w.y), w.y+1+(r.wf.k):X(fr)+1)
_accessibles(fr::Full1DFrame, w::Interval{Int}, r::FilteredRelation{_IA_A,IntervalLengthFilter{==}}) = zip(Iterators.repeated(w.y), w.y+1+(r.wf.k):X(fr)+1)


# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_Ai) = zip(1:w.x-1, Iterators.repeated(w.x))
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_L) = _intervals_in(w.y+1, X(fr)+1)
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_Li) = _intervals_in(1, w.x-1)
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_B) = zip(Iterators.repeated(w.x), w.x+1:w.y-1)
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_Bi) = zip(Iterators.repeated(w.x), w.y+1:X(fr)+1)
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_E) = zip(w.x+1:w.y-1, Iterators.repeated(w.y))
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_Ei) = zip(1:w.x-1, Iterators.repeated(w.y))
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_D) = _intervals_in(w.x+1, w.y-1)
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_Di) = Iterators.product(1:w.x-1, w.y+1:X(fr)+1)
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_O) = Iterators.product(w.x+1:w.y-1, w.y+1:X(fr)+1)
# _accessibles(fr::Full1DFrame, w::Interval{Int}, ::_IA_Oi) = Iterators.product(1:w.x-1, w.x+1:w.y-1)
