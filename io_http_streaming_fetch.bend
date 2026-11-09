# HTTP client: a GET to ip-api.com (208.95.112.1: the TCP kit has no
# DNS) that prints the body of the answer: the status, country, city
# and IP of the caller. Read until EOF (Connection: close), up to
# 65536 bytes including headers. Each buffer received goes through the
# streaming UTF-8 decoder and its text is printed at once, so a slow
# connection shows the text as it arrives. Try it:
#
#   bend io_http_streaming_fetch.bend
import Base
import ./utf8.bend as UTF8

# How far the search for the end of the headers has got: whether the
# window matched, and the window, the last 4 characters as a big-endian
# word. The headers end at the first "\r\n\r\n" (218762506).
def BodyScan() -> Type:
  Bool & U32

def body_scan_start() -> BodyScan():
  (False{}, 0)

# The part of `s` that is body text, given how far the search has got,
# and how far the search has got after `s`. The headers can end in any
# buffer, or across two of them.
def http_body.go(s: String, e: Bool, w: U32) -> BodyScan() & String:
  match s:
    case SNil{}:
      ((e, w), SNil{})
    case SCon{Chr{a}, t}:
      match e:
        case True{}:
          ((True{}, w), SCon{Chr{a}, t})
        case False{}:
          +w2 = (w * 256 + a : U32)
          http_body.go(t, U32.is_eq(w2, 218762506), w2)

def http_body(scan: BodyScan(), s: String) -> BodyScan() & String:
  (e, w) = scan
  http_body.go(s, e, w)

# Print the body text in `s`. IO.write adds no newline, so a line split
# across two buffers prints as one line.
def print_body.write(result: BodyScan() & String) -> IO(BodyScan()):
  (next, body) = result
  do IO<BodyScan()>:
    IO.write(body)
    return next

def print_body(scan: BodyScan(), s: String) -> IO(BodyScan()):
  print_body.write(http_body(scan, s))

# The decoder's state and the search for the body, between buffers.
def Progress() -> Type:
  UTF8.DecodeState() & BodyScan()

def fetch_fail(s: Socket, code: U32, message: String) -> IO(Unit):
  do IO<Unit>:
    Socket.close(s)
    IO.die(Unit, code, message)

# Print what the decoder was still holding: a replacement character if
# the response ended inside a sequence.
def fetch_done(s: Socket, progress: Progress()) -> IO(Unit):
  (state, scan) = progress
  do IO<Unit>:
    Socket.close(s)
    last : BodyScan() <- print_body(scan, UTF8.decode_done(state))
    return Unit{}

def fetch_print.decoded(
  s: Socket,
  decoded: UTF8.DecodeState() & String,
  scan: BodyScan(),
  next: Socket -> Progress() -> IO(Unit)
) -> IO(Unit):
  (state, text) = decoded
  do IO<Unit>:
    scan2 : BodyScan() <- print_body(scan, text)
    next(s, (state, scan2))

# Decode and print a buffer, then go on to `next`. The decoder requires
# every value to be a byte, and the type of TCP.recv_bytes doesn't say
# so, which `ok` tests.
def fetch_print(
  s: Socket,
  +buffer: List<&2, U32>,
  ok: Bool,
  -checked: {UTF8.decode_buffer.all_bytes(buffer) == ok : Bool},
  progress: Progress(),
  next: Socket -> Progress() -> IO(Unit)
) -> IO(Unit):
  match ok:
    case False{}:
      fetch_fail(s, 1, "TCP.recv_bytes returned a value that is not a byte")
    case True{}:
      (state, scan) = progress
      fetch_print.decoded(s, UTF8.decode_buffer(state, buffer, checked), scan, next)

# At the exact limit, the one-byte probe must be EOF.
def fetch_end(
  m: Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>,
  progress: Progress()
) -> IO(Unit):
  (s, r) = m
  match r:
    case Fail{(code, message)}:
      fetch_fail(s, code, message)
    case Done{chunk}:
      match chunk:
        case None{}:
          fetch_done(s, progress)
        case Some{bytes}:
          fetch_fail(s, 1, "HTTP response exceeds 65536 bytes")

def fetch_read(
  fuel: Nat,
  remaining: U32,
  m: Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>,
  progress: Progress()
) -> IO(Unit):
  match fuel remaining:
    case 0n _:
      fetch_end(m, progress)
    case _ 0:
      fetch_end(m, progress)
    case 1n+fuel2 _:
      (s, r) = m
      match r:
        case Fail{(code, message)}:
          fetch_fail(s, code, message)
        case Done{None{}}:
          fetch_done(s, progress)
        case Done{Some{chunk}}:
          match chunk:
            case Nil{}:
              fetch_done(s, progress)
            case +h <> +t:
              +left = U32.sub(remaining, U32.from_nat(List.length(&2, U32, chunk)))
              fetch_print(s, chunk, UTF8.decode_buffer.all_bytes(chunk), {==}, progress,
                s2 => progress2 =>
                  do IO<Unit>:
                    next : Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>> <-
                      TCP.recv_bytes(s2, U32.max(U32.min(left, 8192), 1))
                    fetch_read(fuel2, left, next, progress2))

def fetch_sent(m: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Unit):
  (s, r) = m
  match r:
    case Fail{((code, message), rest)}:
      fetch_fail(s, code, message)
    case Done{u}:
      do IO<Unit>:
        first : Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>> <-
          TCP.recv_bytes(s, 8192)
        fetch_read(65536n, 65536, first, (UTF8.decode_start_state(), body_scan_start()))

def main() -> IO(Unit):
  do IO<Unit>:
    c    : Socket <- IO.try(Socket, TCP.connect("208.95.112.1", 80))
    sent : Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit> <- TCP.send(c, "GET /line/?fields=status,country,city,query HTTP/1.1\r\nHost: ip-api.com\r\nConnection: close\r\n\r\n")
    fetch_sent(sent)
