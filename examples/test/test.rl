/* commuting method calls */

interface A =

  class K { a: int; b: int; }

  meth f (self:K, s:int) : unit
    ensures { self.a = s }
    effects { rw {self}`a; rd self, s }

  meth g (self:K, k:int) : unit
    ensures { self.b = k }
    effects { rw {self}`b; rd self, k }

  meth m (self:K, k:int) : unit
    ensures { self.a = k /\ self.b = k }
    effects { rw {self}`any; rd self, k }

end

module A0 : A =

  class K { a: int; b: int; }

  meth f (self:K, s:int) : unit =
    self.a := s;

  meth g (self:K, k:int) : unit =
    self.b := k;

  meth m (self:K, k:int) : unit =
    f (self, k);
    g (self, k);

end

module A1 : A =

  class K { a: int; b: int; }

  meth f (self:K, s:int) : unit =
    self.a := s;

  meth g (self:K, k:int) : unit =
    self.b := k;

  meth m (self:K, k:int) : unit =
    g (self, k);
    f (self, k);

end

bimodule A_REL (A0 | A1) =

  meth f (self:K, s:int | self:K, s:int) : (unit | unit)
    requires { Agree self }
    requires { Agree s }
    ensures  { Agree {self}`a }
    effects  { rw {self}`a; rd self, s | rw {self}`a; rd self, s }
  = |_ self.a := s _|;

  meth g (self:K, k:int | self:K, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`b }
    effects  { rw {self}`b; rd self, k | rw {self}`b; rd self, k }
  = |_ self.b := k _|;

  meth m (self:K, k:int | self:K, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`a /\ Agree {self}`b }
    effects  { rw {self}`any; rd self, k | rw {self}`any; rd self, k }
  = ( f(self,k) | g(self,k) );
    ( g(self,k) | f(self,k) );

  meth m2 (self:K, k:int | self:K, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`a /\ Agree {self}`b }
    effects  { rw {self}`any; rd self, k | rw {self}`any; rd self, k }
  = ( f(self,k); g(self,k) | g(self,k); f(self,k) );

end
