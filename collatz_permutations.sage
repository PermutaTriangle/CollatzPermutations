from sage.structure.parent import Parent
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets

def u(x):
    """Collatz sequence up-step.
    u(x) = 3*x+1
    """
    return 3*x+1

def d(x):
    """Collatz sequence down-step.
    d(x) = x/2
    """
    try:
        return x//2
    except:
        return x/2

def U(x):
    """Inverse of Collatz sequence up-step.
    U(x) = (x-1)/3
    """
    try:
        return (x-1)//3
    except:
        return (x-1)/3

def D(x):
    """Inverse of Collatz sequence down-step.
    D(x) = 2*x
    """
    return 2*x

def _get_inverse_step(step):
    """Returns the inverse of a Collatz step."""
    return {
        u: U, U: u,
        d: D, D: d,
    }[step]

def _get_next_collatz_step(x):
    """Returns the next step that should be taken after x in the Collatz
    sequence."""
    if x % 2 == 0:
        return d
    else:
        return u

def _is_power_of_two(x):
    """Determines if x is a power of two."""
    return (x & (x - 1)) == 0

def to_standard(lst):
    """Converts a list of distinct elements into a permutation by replacing the
    i-th smallest element with the integer i."""
    result = [0 for i in range(len(lst))]
    for i, (_, j) in enumerate(sorted( (lst[j], j) for j in range(len(lst)) )):
        result[j] = i+1
    return Permutation(result)



class OperationSequences(Parent):
    """A class representing all operation sequences of length n."""

    def __init__(self, n):
        self.n = n
        Parent.__init__(self, category = FiniteEnumeratedSets())

    def __iter__(self):

        def bt(l, n):
            if n == 0:
                yield l
            else:
                for os in bt(l + [d], n - 1):
                    yield os

                if n > 1 and (len(l) == 0 or l[-1] != u):
                    for os in bt(l + [u], n - 1):
                        yield os

        for os in bt([], self.n):
            yield OperationSequence(os)

    def cardinality(self):
        """The number of operation sequences of length n."""
        return fibonacci(self.n + 1)

    def unrank(self, r):
        """Returns the r-th operation sequence of length n in their
        lexicographic ordering."""
        assert 0 <= r < self.cardinality()

        if self.n == 0:
            return OperationSequence([])
        elif self.n == 1:
            return OperationSequence([d])

        left = OperationSequences(self.n - 1)
        right = OperationSequences(self.n - 2)

        if r < left.cardinality():
            return OperationSequence([d] + left.unrank(r).opseq)
        else:
            return OperationSequence([u,d] + right.unrank(r - left.cardinality()).opseq)

    def rank(self, x):
        """Returns the index of the operation sequence x in the lexicographic
        ordering of operation sequences of length n."""
        assert len(x) == self.n

        left = OperationSequences(self.n - 1)
        right = OperationSequences(self.n - 2)

        if self.n == 0:
            assert x.opseq == []
            return 0
        elif self.n == 1:
            assert x.opseq == [d]
            return 0

        if x.opseq[:1] == [d]:
            return left.rank(OperationSequence(x.opseq[1:]))
        elif x.opseq[:2] == [u,d]:
            return right.rank(OperationSequence(x.opseq[2:])) + left.cardinality()
        else:
            assert False


class OperationSequence(Parent):
    """A class representing a single operation sequence."""

    def __init__(self, opseq):
        self.opseq = opseq
        Parent.__init__(self)

    @staticmethod
    def from_initial_number(x, include_tail=False):
        """Constructs an operation sequence from a given initial number."""
        opseq = []
        if include_tail:
            while x != 1:
                op = _get_next_collatz_step(x)
                opseq.append(op)
                x = op(x)
        elif x != 1:
            while True:
                op = _get_next_collatz_step(x)
                nxt = op(x)
                if is_power_of_two(nxt):
                    break

                opseq.append(op)
                x = nxt

        return OperationSequence(opseq)

    def get_inverse(self):
        """Returns the inverse of the current operation sequence."""
        return OperationSequence([ _get_inverse_step(op) for op in self ][::-1])

    def get_modular_requirement(self):
        """Returns the modular requirement of the current operation
        sequence."""
        A = var('A')
        x = self.get_inverse()(U(A))

        # now x = (2^l * A - d) / 3^(i-l)

        denom = int(denominator(x))
        x *= denom
        right = int(-x.subs(A=0))
        left = int(x.subs(A=1) + right)

        # A needs to be an integer, so
        # left * A - right = 0 (mod denom)
        # or
        # A = inverse_mod(left, denom) * right (mod denom)

        return (
            (inverse_mod(left, denom) * right) % denom,
            denom
        )

    def get_all_initial_numbers(self):
        """Returns all initial numbers that are witnesses to the current
        operation sequence."""
        a = 1
        c, m = self.get_modular_requirement()
        while power_mod(2, a, m) != c:
            a += 1

        two_pow_a = 2**a
        k = 0
        tmp_m = m
        while tmp_m > 1:
            k += 1
            tmp_m //= 3

        while True:
            init = self.get_inverse()(U(two_pow_a))
            # if all( not is_power_of_two(x) for x in self.get_collatz_sequence(init) ):
            if OperationSequence.from_initial_number(init) == self:
                yield init
            two_pow_a *= 2**(2 * 3**k)

    def get_intersection_points(self):
        """Returns all intersection points of the current operation sequence
        viewed as lines."""

        f = var('x')
        lines = []
        for op in [U] + self.get_inverse().opseq:
            f = op(f)
            lines.append((len(lines), (f - f.subs(x=0))/x, f.subs(x=0)))

        res = []
        for i in range(len(lines)):
            for j in range(i+1, len(lines)):
                res.append((lines[j][2] - lines[i][2]) / (lines[i][1] - lines[j][1]))

        return res

    def get_largest_intersection_point(self):
        """Returns the largest intersection points of the current operation
        sequence viewed as lines."""
        return max(self.get_intersection_points())

    def get_trace(self, x):
        """Returns the trace of the given initial number."""
        res = [x]
        for op in self.opseq:
            x = op(x)
            res.append(x)
        return res

    def get_all_permutations(self):
        """Returns all Collatz permutations produced by the current operation
        sequence."""
        res = []
        it = self.get_largest_intersection_point()
        for x in self.get_all_initial_numbers():
            seq = self.get_collatz_sequence(x)
            perm = to_standard(seq)
            res.append(perm)
            tail = u(seq[-1])
            if tail > it:
                break
        return res

    def __repr__(self):
        return 'OperationSequence([%s])' % ','.join( str(op.__name__) for op in self.opseq )

    def __str__(self):
        return ''.join( str(op.__name__) for op in self.opseq )

    def __len__(self):
        return len(self.opseq)

    def __iter__(self):
        return iter(self.opseq)

    def __getitem__(self, *args):
        res = self.opseq.__getitem__(*args)
        if type(res) is not list: res = [res]
        return OperationSequence(res)

    def __call__(self, x):
        for op in self:
            x = op(x)
        return x

    def __eq__(self, other):
        return isinstance(other, OperationSequence) and self.opseq == other.opseq

    def __hash__(self):
        h = 1
        for op in self.opseq:
            h <<= 1
            if op == d:
                h |= 1
        return int(h)


