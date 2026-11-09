# HTTP client: a GET to ip-api.com (208.95.112.1: the TCP kit has no
# DNS) that prints the body of the answer: the status, country, city
# and IP of the caller. Read until EOF (Connection: close), up to
# 65536 bytes including headers. `fetch_next` receives one buffer,
# runs it through the streaming UTF-8 decoder, and returns its body
# text along with the connection. The client decides what to do with
# the text and when to ask for more; here it prints the text at once,
# so a slow connection shows the text as it arrives. Try it:
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

# The most bytes a response may have, including headers.
def fetch_limit() -> U32:
  65536

# An open connection, between buffers: the socket, how many more bytes
# may be read, the decoder's state, and the search for the body.
type Connection is Type:
  Connection{socket: Socket, remaining: U32, state: UTF8.DecodeState(), scan: BodyScan()}

# What receiving a buffer produced: body text and the connection to
# read more from, or the last body text with the connection closed.
type FetchStep is Type:
  FetchMore{text: String, connection: Connection}
  FetchLast{text: String}

def fetch_fail(-A: Type, s: Socket, code: U32, message: String) -> IO(A):
  do IO<A>:
    Socket.close(s)
    IO.die(A, code, message)

def fetch_last(result: BodyScan() & String) -> FetchStep:
  (scan, body) = result
  FetchLast{body}

# Give what the decoder was still holding: a replacement character if
# the response ended inside a sequence.
def fetch_done(s: Socket, state: UTF8.DecodeState(), scan: BodyScan()) -> IO(FetchStep):
  do IO<FetchStep>:
    Socket.close(s)
    return fetch_last(http_body(scan, UTF8.decode_done(state)))

def fetch_more.scanned(s: Socket, left: U32, state: UTF8.DecodeState(),
  result: BodyScan() & String) -> FetchStep:
  (scan, body) = result
  FetchMore{body, Connection{s, left, state, scan}}

def fetch_more(s: Socket, left: U32, decoded: UTF8.DecodeState() & String,
  scan: BodyScan()) -> FetchStep:
  (state, text) = decoded
  fetch_more.scanned(s, left, state, http_body(scan, text))

# The decoder requires every value to be a byte, and the type of
# TCP.recv_bytes doesn't say so, which `ok` tests.
def fetch_decode(
  s: Socket,
  +buffer: List<&2, U32>,
  ok: Bool,
  -checked: {UTF8.decode_buffer.all_bytes(buffer) == ok : Bool},
  left: U32,
  state: UTF8.DecodeState(),
  scan: BodyScan()
) -> IO(FetchStep):
  match ok:
    case False{}:
      fetch_fail(FetchStep, s, 1, "TCP.recv_bytes returned a value that is not a byte")
    case True{}:
      do IO<FetchStep>:
        return fetch_more(s, left, UTF8.decode_buffer(state, buffer, checked), scan)

# At the exact limit, the one-byte probe must be EOF.
def fetch_end(
  m: Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>,
  state: UTF8.DecodeState(),
  scan: BodyScan()
) -> IO(FetchStep):
  (s, r) = m
  match r:
    case Fail{(code, message)}:
      fetch_fail(FetchStep, s, code, message)
    case Done{None{}}:
      fetch_done(s, state, scan)
    case Done{Some{bytes}}:
      fetch_fail(FetchStep, s, 1, "HTTP response exceeds " ++ U32.show(fetch_limit()) ++ " bytes")

def fetch_received(
  remaining: U32,
  m: Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>,
  state: UTF8.DecodeState(),
  scan: BodyScan()
) -> IO(FetchStep):
  match remaining:
    case 0:
      fetch_end(m, state, scan)
    case _:
      (s, r) = m
      match r:
        case Fail{(code, message)}:
          fetch_fail(FetchStep, s, code, message)
        case Done{None{}}:
          fetch_done(s, state, scan)
        case Done{Some{chunk}}:
          match chunk:
            case Nil{}:
              fetch_done(s, state, scan)
            case +h <> +t:
              +left = U32.sub(remaining, U32.from_nat(List.length(&2, U32, chunk)))
              fetch_decode(s, chunk, UTF8.decode_buffer.all_bytes(chunk), {==}, left, state, scan)

# Receive the next buffer.
def fetch_next(connection: Connection) -> IO(FetchStep):
  match connection:
    case Connection{s, +remaining, state, scan}:
      do IO<FetchStep>:
        m : Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>> <-
          TCP.recv_bytes(s, U32.max(U32.min(remaining, 8192), 1))
        fetch_received(remaining, m, state, scan)

def fetch_close(connection: Connection) -> IO(Unit):
  match connection:
    case Connection{s, remaining, state, scan}:
      Socket.close(s)

def fetch_start(m: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Connection):
  (s, r) = m
  match r:
    case Fail{((code, message), rest)}:
      fetch_fail(Connection, s, code, message)
    case Done{u}:
      do IO<Connection>:
        return Connection{s, fetch_limit(), UTF8.decode_start_state(), body_scan_start()}

# The client's loop. `fuel` satisfies Bend's termination check: every
# FetchMore has used up at least one of the allowed bytes, so fuel equal
# to `fetch_limit()` is enough and the 0n case can't happen. IO.write
# adds no newline, so a line split across two buffers prints as one line.
def print_steps(fuel: Nat, step: FetchStep) -> IO(Unit):
  match fuel step:
    case _ FetchLast{text}:
      IO.write(text)
    case 0n FetchMore{text, connection}:
      fetch_close(connection)
    case 1n+fuel2 FetchMore{text, connection}:
      do IO<Unit>:
        IO.write(text)
        next : FetchStep <- fetch_next(connection)
        print_steps(fuel2, next)

def main() -> IO(Unit):
  do IO<Unit>:
    c          : Socket <- IO.try(Socket, TCP.connect("208.95.112.1", 80))
    sent       : Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit> <- TCP.send(c, "GET /line/?fields=status,country,city,query HTTP/1.1\r\nHost: ip-api.com\r\nConnection: close\r\n\r\n")
    connection : Connection <- fetch_start(sent)
    first      : FetchStep <- fetch_next(connection)
    print_steps(U32.to_nat(fetch_limit()), first)
