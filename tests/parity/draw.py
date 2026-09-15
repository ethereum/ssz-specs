"""Where a generated corpus gets its choices."""

import random
from collections.abc import Callable, Sequence
from typing import Self

from hypothesis import strategies as st


class Draw:
    """A source of choices, so one generator serves both a seeded run and a searching one."""

    def __init__(self, choose: Callable[[int], int]) -> None:
        self.choose = choose
        """Answers a bound with a number below it."""

    @classmethod
    def seeded(cls, seed: int) -> Self:
        """Choices a seed fixes, so two runs draw the same corpus."""
        return cls(random.Random(seed).randrange)

    @classmethod
    def searched(cls, data: st.DataObject) -> Self:
        """Choices the search makes, and shrinks when one of them fails."""
        return cls(lambda bound: data.draw(st.integers(0, bound - 1)))

    def below(self, bound: int) -> int:
        """A number below the bound, and zero where the bound leaves no choice."""
        return self.choose(bound) if bound > 1 else 0

    def between(self, low: int, high: int) -> int:
        """A number in an inclusive range."""
        return low + self.below(high - low + 1)

    def pick[T](self, options: Sequence[T]) -> T:
        """One of the options."""
        return options[self.below(len(options))]

    def flag(self) -> bool:
        """A boolean."""
        return self.below(2) == 1
