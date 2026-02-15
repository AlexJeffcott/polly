import type { P2PMessage } from "../types";

interface PeerConnectionConfig {
  peerId: string;
  displayName: string;
  initiator: boolean; // true if we create the offer
  onMessage: (message: P2PMessage) => void;
  onStateChange: (state: RTCPeerConnectionState) => void;
  onIceCandidate: (candidate: RTCIceCandidateInit) => void;
}

/**
 * PeerConnection - Manages WebRTC connection to a single peer
 *
 * Responsibilities:
 * - Create and manage RTCPeerConnection
 * - Handle SDP offer/answer exchange
 * - Manage ICE candidates
 * - Create and manage data channel
 * - Send/receive P2P messages
 */
export class PeerConnection {
  private pc: RTCPeerConnection;
  private channel: RTCDataChannel | null = null;
  private pingInterval: number | null = null;

  constructor(private config: PeerConnectionConfig) {
    // Use free STUN servers for NAT traversal
    // In production, you'd want TURN servers too for reliability
    this.pc = new RTCPeerConnection({
      iceServers: [
        { urls: "stun:stun.l.google.com:19302" },
        { urls: "stun:stun1.l.google.com:19302" },
      ],
    });

    this.setupEventHandlers();

    // Initiator creates the data channel
    if (config.initiator) {
      this.createDataChannel();
    }
  }

  /**
   * Set up RTCPeerConnection event handlers
   */
  private setupEventHandlers() {
    // ICE candidate discovered - send to other peer via signaling
    this.pc.onicecandidate = (event) => {
      if (event.candidate) {
        this.config.onIceCandidate(event.candidate.toJSON());
      }
    };

    // Connection state changed
    this.pc.onconnectionstatechange = () => {
      console.log(`Connection state (${this.config.peerId}): ${this.pc.connectionState}`);
      this.config.onStateChange(this.pc.connectionState);

      if (this.pc.connectionState === "connected") {
        this.startPingPong();
      } else if (
        this.pc.connectionState === "disconnected" ||
        this.pc.connectionState === "failed"
      ) {
        this.stopPingPong();
      }
    };

    // Data channel received (for non-initiator)
    this.pc.ondatachannel = (event) => {
      console.log(`📡 Received data channel from ${this.config.peerId}`);
      this.channel = event.channel;
      this.setupDataChannel();
    };
  }

  /**
   * Create data channel (initiator only)
   */
  private createDataChannel() {
    this.channel = this.pc.createDataChannel("chat", {
      ordered: true, // Messages arrive in order
    });
    console.log(`📡 Created data channel to ${this.config.peerId}`);
    this.setupDataChannel();
  }

  /**
   * Set up data channel event handlers
   */
  private setupDataChannel() {
    if (!this.channel) return;

    this.channel.onopen = () => {
      console.log(`✅ Data channel open (${this.config.peerId})`);
    };

    this.channel.onclose = () => {
      console.log(`🔌 Data channel closed (${this.config.peerId})`);
    };

    this.channel.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data) as P2PMessage;
        this.config.onMessage(message);
      } catch (error) {
        console.error("Failed to parse P2P message:", error);
      }
    };

    this.channel.onerror = (error) => {
      console.error(`Data channel error (${this.config.peerId}):`, error);
    };
  }

  /**
   * Create WebRTC offer
   */
  async createOffer(): Promise<RTCSessionDescriptionInit> {
    const offer = await this.pc.createOffer();
    await this.pc.setLocalDescription(offer);
    return offer;
  }

  /**
   * Handle incoming WebRTC offer and create answer
   */
  async handleOffer(offer: RTCSessionDescriptionInit): Promise<RTCSessionDescriptionInit> {
    await this.pc.setRemoteDescription(offer);
    const answer = await this.pc.createAnswer();
    await this.pc.setLocalDescription(answer);
    return answer;
  }

  /**
   * Handle incoming WebRTC answer
   */
  async handleAnswer(answer: RTCSessionDescriptionInit) {
    await this.pc.setRemoteDescription(answer);
  }

  /**
   * Add ICE candidate
   */
  async addIceCandidate(candidate: RTCIceCandidateInit) {
    try {
      await this.pc.addIceCandidate(candidate);
    } catch (error) {
      console.error("Error adding ICE candidate:", error);
    }
  }

  /**
   * Send a message over the data channel
   */
  send(message: P2PMessage) {
    if (this.channel?.readyState === "open") {
      this.channel.send(JSON.stringify(message));
    } else {
      console.error("❌ Cannot send, data channel not open");
    }
  }

  /**
   * Start ping/pong for latency measurement
   */
  private startPingPong() {
    this.pingInterval = window.setInterval(() => {
      this.send({ type: "ping", timestamp: Date.now() });
    }, 5000);
  }

  /**
   * Stop ping/pong
   */
  private stopPingPong() {
    if (this.pingInterval) {
      clearInterval(this.pingInterval);
      this.pingInterval = null;
    }
  }

  /**
   * Close the connection
   */
  close() {
    this.stopPingPong();
    this.channel?.close();
    this.pc.close();
  }

  /**
   * Get current connection state
   */
  get connectionState(): RTCPeerConnectionState {
    return this.pc.connectionState;
  }
}
