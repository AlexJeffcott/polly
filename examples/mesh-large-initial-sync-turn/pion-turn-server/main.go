// Pion TURN server for polly issue #105's falsification harness.
//
// Boots a single-realm TURN server on UDP at the address given via
// -addr (default 127.0.0.1:0 — kernel picks the port and the program
// prints it on stdout as `listening udp=HOST:PORT`). The auth model is
// the use-auth-secret / long-term-auth-secret pattern that production
// coturn deployments use: the shared secret is read from -secret, and
// the username sent by the client is "<unix-expiry-timestamp>:<peer>".
// The password is HMAC-SHA1(secret, username), base64-encoded.
//
// The harness generates its own short-lived credentials for each peer
// and sets ICEServer.{username,credential} accordingly. Nothing about
// the auth path differs from the Fly-hosted coturn the issue file is
// written against, so a failure in this harness is a failure that
// would also surface against that relay.
package main

import (
	"crypto/hmac"
	"crypto/sha1"
	"encoding/base64"
	"errors"
	"flag"
	"fmt"
	"net"
	"os"
	"os/signal"
	"strconv"
	"strings"
	"syscall"
	"time"

	"github.com/pion/logging"
	"github.com/pion/turn/v4"
)

func main() {
	addrFlag := flag.String("addr", "127.0.0.1:0", "listen address for the UDP TURN server")
	secretFlag := flag.String("secret", "", "shared HMAC secret for use-auth-secret credentials (required)")
	realmFlag := flag.String("realm", "polly.local", "TURN realm")
	flag.Parse()

	if *secretFlag == "" {
		fmt.Fprintln(os.Stderr, "pion-turn-server: -secret is required")
		os.Exit(2)
	}

	udpListener, err := net.ListenPacket("udp4", *addrFlag)
	if err != nil {
		fmt.Fprintf(os.Stderr, "pion-turn-server: failed to bind udp %s: %v\n", *addrFlag, err)
		os.Exit(1)
	}
	bound := udpListener.LocalAddr().(*net.UDPAddr)

	// The relay address we hand out to clients. The harness runs every
	// peer on 127.0.0.1, so the relay can also bind on 127.0.0.1 — and
	// must, because Pion's default RelayAddressGenerator returns the
	// IP it sees the source request arrive on, which for loopback is
	// 127.0.0.1 anyway. Pinning the relay IP here makes the loopback
	// constraint explicit.
	relayIP := bound.IP
	if relayIP == nil || relayIP.IsUnspecified() {
		relayIP = net.ParseIP("127.0.0.1")
	}

	server, err := turn.NewServer(turn.ServerConfig{
		Realm:       *realmFlag,
		AuthHandler: authHandler(*secretFlag, *realmFlag),
		PacketConnConfigs: []turn.PacketConnConfig{
			{
				PacketConn: udpListener,
				RelayAddressGenerator: &turn.RelayAddressGeneratorStatic{
					RelayAddress: relayIP,
					Address:      "127.0.0.1",
				},
			},
		},
		LoggerFactory: logging.NewDefaultLoggerFactory(),
	})
	if err != nil {
		fmt.Fprintf(os.Stderr, "pion-turn-server: failed to construct server: %v\n", err)
		os.Exit(1)
	}

	// stdout is the structured channel the harness reads to learn where
	// to point its ICE servers. Print once, fully formed, then keep
	// stdout free of further output so the harness's parser stays
	// trivial. Diagnostics go to stderr.
	fmt.Printf("listening udp=%s realm=%s\n", bound.String(), *realmFlag)

	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	<-sigCh

	if err := server.Close(); err != nil && !errors.Is(err, net.ErrClosed) {
		fmt.Fprintf(os.Stderr, "pion-turn-server: shutdown error: %v\n", err)
		os.Exit(1)
	}
}

// authHandler implements the long-term-auth-secret scheme. Pion calls
// this for every Allocate request with the username the client placed
// in the STUN message; we return the HMAC-SHA1(secret, username) bytes
// the server will compare against the client's MessageIntegrity, plus
// the realm. The expiry encoded in the username is informational; the
// validation is the HMAC match alone, which is the same semantics as
// coturn use-auth-secret.
func authHandler(secret, realm string) turn.AuthHandler {
	return func(username string, _ string, _ net.Addr) ([]byte, bool) {
		// Username shape per coturn use-auth-secret: "<unix-expiry>:<peer>"
		// — the expiry half is purely advisory, the HMAC is the auth.
		if username == "" {
			return nil, false
		}
		parts := strings.SplitN(username, ":", 2)
		if len(parts) != 2 {
			return nil, false
		}
		if expiry, err := strconv.ParseInt(parts[0], 10, 64); err == nil {
			if expiry > 0 && time.Now().Unix() > expiry {
				return nil, false
			}
		}
		mac := hmac.New(sha1.New, []byte(secret))
		mac.Write([]byte(username))
		password := base64.StdEncoding.EncodeToString(mac.Sum(nil))
		key := turn.GenerateAuthKey(username, realm, password)
		return key, true
	}
}
