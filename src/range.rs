//
// Copyright 2021 Hans W. Uhlig. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use crate::{Coordinate, Integer};
use num::{One, Zero};
use std::cmp::{max, min};

/// Iterator over an range
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct RangeIter<I: Integer> {
    source: Coordinate<I>,
    x: I,
    y: I,
    r: I,
    counter: usize,
}

impl<I: Integer> RangeIter<I> {
    /// Create a new Range Iterator
    pub(crate) fn new(origin: &Coordinate<I>, radius: I) -> RangeIter<I> {
        RangeIter {
            source: origin.clone(),
            x: -radius,
            y: max(-radius, -(-radius) - radius),
            r: radius,
            counter: 0,
        }
    }
}

impl<I: Integer> Iterator for RangeIter<I> {
    type Item = Coordinate<I>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.y > min(self.r, -self.x + self.r) {
            if self.x >= self.r {
                return None;
            }
            self.x += One::one();
            self.y = max(-self.r, -self.x - self.r);
        }

        let ret = Some(Coordinate {
            x: self.source.x + self.x,
            y: self.source.y + self.y,
        });
        self.y += One::one();
        self.counter += 1;
        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rc = (if self.r < Zero::zero() {
            I::one() - self.r
        } else {
            self.r
        })
        .to_usize()
        .unwrap();
        let total_size = 3 * (rc + rc * rc) + 1;
        let current_size = total_size - self.counter;
        (current_size, Some(current_size))
    }
}

impl<I: Integer> std::iter::FusedIterator for RangeIter<I> {}
impl<I: Integer> std::iter::ExactSizeIterator for RangeIter<I> {}
