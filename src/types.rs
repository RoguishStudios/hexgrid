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

/// Integer trait used by this library.
pub trait Integer:
    num::Signed
    + num::Integer
    + num::CheckedAdd
    + num::ToPrimitive
    + num::FromPrimitive
    + num::NumCast
    + num::One
    + num::Zero
    + std::default::Default
    + std::fmt::Debug
    + std::hash::Hash
    + std::marker::Copy
    + std::ops::AddAssign
{
}

impl<I> Integer for I where
    I: num::Signed
        + num::Integer
        + num::CheckedAdd
        + num::ToPrimitive
        + num::FromPrimitive
        + num::NumCast
        + num::One
        + num::Zero
        + std::default::Default
        + std::fmt::Debug
        + std::hash::Hash
        + std::marker::Copy
        + std::ops::AddAssign
{
}

/// Float trait used by this library
pub trait Float:
    num::Signed
    + num::Float
    + num::ToPrimitive
    + num::FromPrimitive
    + num::NumCast
    + num::One
    + num::Zero
    + std::marker::Copy
    + std::ops::AddAssign
    + std::default::Default
{
}

impl<F> Float for F where
    F: num::Signed
        + num::Float
        + num::ToPrimitive
        + num::FromPrimitive
        + num::NumCast
        + num::One
        + num::Zero
        + std::marker::Copy
        + std::ops::AddAssign
        + std::default::Default
{
}
