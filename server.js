const express  = require('express');
const http     = require('http');
const socketIO = require('socket.io');
const cors     = require('cors');
const fs       = require('fs');
const path     = require('path');

const app    = express();
const server = http.createServer(app);

// ─────────────────────────────────────────────
//  Constants
// ─────────────────────────────────────────────
const MAX_MESSAGE_LENGTH     = 500;
const MAX_USERNAME_LENGTH    = 32;
const MAX_HISTORY            = 50;
const CODE_LENGTH            = 9;

// Verify rate-limit
const MAX_VERIFY_ATTEMPTS    = 5;
const VERIFY_WINDOW_MS       = 60 * 1000;

// Chat message rate-limit (per socket)
const MSG_RATE_MAX           = 4;           // max messages …
const MSG_RATE_WINDOW_MS     = 3000;        // … per 3 seconds

// IP-level verify rate-limit
const MAX_VERIFY_ATTEMPTS_IP = 15;
const VERIFY_IP_WINDOW_MS    = 60 * 1000;

const MAX_SESSIONS_PER_CODE  = 3;
const UNVERIFIED_TIMEOUT_MS  = 30 * 1000;  // kick unverified after 30 s

// Prevent codeUsage memory growth
const MAX_CODE_USAGE_ENTRIES = 20;

// ─────────────────────────────────────────────
//  Environment Variables
// ─────────────────────────────────────────────
const DISCORD_WEBHOOK_LOGS = process.env.DISCORD_WEBHOOK_LOGS;
const DISCORD_WEBHOOK_CHAT = process.env.DISCORD_WEBHOOK_CHAT;
const ADMIN_SECRET         = process.env.ADMIN_SECRET;

// For Render.com: ALLOWED_ORIGIN should be set to 'https://starblast.io' in env vars.
// During local dev you can set it to '*' or 'http://localhost:PORT'.
const ALLOWED_ORIGIN = process.env.ALLOWED_ORIGIN || 'https://starblast.io';

// ─────────────────────────────────────────────
//  LZ-String (server-side, for Discord logging)
//  Inline implementation — no extra npm dep needed.
// ─────────────────────────────────────────────
// Minimal decompressFromUTF16 port so Discord logs show readable text.
// Source: https://github.com/pieroxy/lz-string (MIT)
const LZString = (() => {
    const keyStrUriSafe = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-$';
    const baseReverseDic = {};

    function getBaseValue(alphabet, character) {
        if (!baseReverseDic[alphabet]) {
            baseReverseDic[alphabet] = {};
            for (let i = 0; i < alphabet.length; i++) {
                baseReverseDic[alphabet][alphabet.charAt(i)] = i;
            }
        }
        return baseReverseDic[alphabet][character];
    }

    function _decompress(length, resetValue, getNextValue) {
        const dictionary = [];
        let next, enlargeIn = 4, dictSize = 4, numBits = 3, entry = '', result = [];
        let i, w, bits, resb, maxpower, power, c;
        let data = { val: getNextValue(0), position: resetValue, index: 1 };

        for (i = 0; i < 3; i++) dictionary[i] = i;

        bits = 0; maxpower = Math.pow(2, 2); power = 1;
        while (power != maxpower) {
            resb = data.val & data.position;
            data.position >>= 1;
            if (data.position == 0) {
                data.position = resetValue;
                data.val = getNextValue(data.index++);
            }
            bits |= (resb > 0 ? 1 : 0) * power;
            power <<= 1;
        }

        switch (next = bits) {
            case 0:
                bits = 0; maxpower = Math.pow(2, 8); power = 1;
                while (power != maxpower) {
                    resb = data.val & data.position;
                    data.position >>= 1;
                    if (data.position == 0) { data.position = resetValue; data.val = getNextValue(data.index++); }
                    bits |= (resb > 0 ? 1 : 0) * power;
                    power <<= 1;
                }
                c = String.fromCharCode(bits);
                break;
            case 1:
                bits = 0; maxpower = Math.pow(2, 16); power = 1;
                while (power != maxpower) {
                    resb = data.val & data.position;
                    data.position >>= 1;
                    if (data.position == 0) { data.position = resetValue; data.val = getNextValue(data.index++); }
                    bits |= (resb > 0 ? 1 : 0) * power;
                    power <<= 1;
                }
                c = String.fromCharCode(bits);
                break;
            case 2:
                return '';
        }

        dictionary[3] = c; w = c; result.push(c);

        while (true) {
            if (data.index > length) return '';

            bits = 0; maxpower = Math.pow(2, numBits); power = 1;
            while (power != maxpower) {
                resb = data.val & data.position;
                data.position >>= 1;
                if (data.position == 0) { data.position = resetValue; data.val = getNextValue(data.index++); }
                bits |= (resb > 0 ? 1 : 0) * power;
                power <<= 1;
            }

            switch (c = bits) {
                case 0:
                    bits = 0; maxpower = Math.pow(2, 8); power = 1;
                    while (power != maxpower) {
                        resb = data.val & data.position;
                        data.position >>= 1;
                        if (data.position == 0) { data.position = resetValue; data.val = getNextValue(data.index++); }
                        bits |= (resb > 0 ? 1 : 0) * power;
                        power <<= 1;
                    }
                    dictionary[dictSize++] = String.fromCharCode(bits);
                    c = dictSize - 1;
                    enlargeIn--;
                    break;
                case 1:
                    bits = 0; maxpower = Math.pow(2, 16); power = 1;
                    while (power != maxpower) {
                        resb = data.val & data.position;
                        data.position >>= 1;
                        if (data.position == 0) { data.position = resetValue; data.val = getNextValue(data.index++); }
                        bits |= (resb > 0 ? 1 : 0) * power;
                        power <<= 1;
                    }
                    dictionary[dictSize++] = String.fromCharCode(bits);
                    c = dictSize - 1;
                    enlargeIn--;
                    break;
                case 2:
                    return result.join('');
            }

            if (enlargeIn == 0) { enlargeIn = Math.pow(2, numBits); numBits++; }

            if (dictionary[c]) { entry = dictionary[c]; }
            else if (c === dictSize) { entry = w + w.charAt(0); }
            else { return null; }

            result.push(entry);
            dictionary[dictSize++] = w + entry.charAt(0);
            enlargeIn--;
            if (enlargeIn == 0) { enlargeIn = Math.pow(2, numBits); numBits++; }
            w = entry;
        }
    }

    function decompressFromUTF16(compressed) {
        if (compressed == null) return '';
        if (compressed == '') return null;
        return _decompress(compressed.length, 16384, (index) => {
            return compressed.charCodeAt(index) - 32;
        });
    }

    return { decompressFromUTF16 };
})();

// ─────────────────────────────────────────────
//  Socket.IO — restricted CORS
// ─────────────────────────────────────────────
const io = socketIO(server, {
    cors: {
        origin:      ALLOWED_ORIGIN,
        methods:     ['GET', 'POST'],
        credentials: true
    }
});

app.use(cors({ origin: ALLOWED_ORIGIN }));
app.use(express.json());

// ─────────────────────────────────────────────
//  Admin Auth Middleware
// ─────────────────────────────────────────────
function requireAdminAuth(req, res, next) {
    if (!ADMIN_SECRET) {
        return res.status(503).json({ error: 'Admin access not configured. Set ADMIN_SECRET env var.' });
    }
    const token = req.headers['x-admin-token'];
    if (!token || token !== ADMIN_SECRET) {
        return res.status(401).json({ error: 'Unauthorized' });
    }
    next();
}

// ─────────────────────────────────────────────
//  Input Validation Helpers
// ─────────────────────────────────────────────
function sanitizeString(str, maxLength) {
    if (typeof str !== 'string') return null;
    return str.trim().slice(0, maxLength);
}

function isValidUsername(username) {
    if (!username || typeof username !== 'string') return false;
    const trimmed = username.trim();
    if (trimmed.length < 1 || trimmed.length > MAX_USERNAME_LENGTH) return false;
    return /^[a-zA-Z0-9_\- ]+$/.test(trimmed);
}

function isValidMessage(message) {
    if (!message || typeof message !== 'string') return false;
    const trimmed = message.trim();
    return trimmed.length > 0 && trimmed.length <= MAX_MESSAGE_LENGTH;
}

function isValidHexColor(color) {
    return typeof color === 'string' && /^#[0-9a-fA-F]{6}$/.test(color);
}

// Hue must be a number in [0, 360]
function isValidHue(hue) {
    return hue === null || hue === undefined || (typeof hue === 'number' && isFinite(hue) && hue >= 0 && hue <= 360);
}

// ─────────────────────────────────────────────
//  Circular Buffer
// ─────────────────────────────────────────────
class CircularBuffer {
    constructor(size) {
        this.size   = size;
        this.buffer = new Array(size);
        this.head   = 0;
        this.count  = 0;
    }
    push(item) {
        this.buffer[this.head] = item;
        this.head  = (this.head + 1) % this.size;
        this.count = Math.min(this.count + 1, this.size);
    }
    toArray() {
        if (this.count < this.size) {
            return this.buffer.slice(0, this.count).filter(Boolean);
        }
        return [
            ...this.buffer.slice(this.head),
            ...this.buffer.slice(0, this.head)
        ].filter(Boolean);
    }
}

// ─────────────────────────────────────────────
//  Discord Webhook Queue
// ─────────────────────────────────────────────
const discordQueue = [];
let discordProcessing = false;

async function sendDiscordWebhook(webhookUrl, content, embed = null) {
    if (!webhookUrl) return;
    discordQueue.push({ webhookUrl, content, embed });
    if (!discordProcessing) processDiscordQueue();
}

async function processDiscordQueue() {
    if (discordQueue.length === 0) { discordProcessing = false; return; }
    discordProcessing = true;
    const { webhookUrl, content, embed } = discordQueue.shift();
    try {
        const payload = {};
        if (content) payload.content = content;
        if (embed)   payload.embeds  = [embed];
        const response = await fetch(webhookUrl, {
            method:  'POST',
            headers: { 'Content-Type': 'application/json' },
            body:    JSON.stringify(payload)
        });
        if (!response.ok) console.error('Discord Webhook Error:', response.status);
    } catch (error) {
        console.error('Discord Webhook Error:', error.message);
    }
    setTimeout(processDiscordQueue, 500);
}

// ─────────────────────────────────────────────
//  Discord Log Functions
// ─────────────────────────────────────────────
function discordLogSuccess(username, code) {
    sendDiscordWebhook(DISCORD_WEBHOOK_LOGS, null, {
        title:       '✅ Successful Verification',
        description: `**${username}** has verified`,
        color:       0x00ff88,
        fields:      [
            { name: 'Code', value: code, inline: true },
            { name: 'Time', value: new Date().toLocaleString('en-US'), inline: true }
        ],
        timestamp: new Date().toISOString()
    });
}

function discordLogFailed(username, code) {
    sendDiscordWebhook(DISCORD_WEBHOOK_LOGS, null, {
        title:       '❌ Failed Verification',
        description: `**${username}** tried invalid code`,
        color:       0xff0000,
        fields:      [
            { name: 'Attempted Code', value: code, inline: true },
            { name: 'Time', value: new Date().toLocaleString('en-US'), inline: true }
        ],
        timestamp: new Date().toISOString()
    });
}

function discordLogConnect(username, code) {
    sendDiscordWebhook(DISCORD_WEBHOOK_LOGS, null, {
        title:       '🔌 User Connected',
        description: `**${username}** joined the chat`,
        color:       0x0099ff,
        fields:      [
            { name: 'Code', value: code, inline: true },
            { name: 'Time', value: new Date().toLocaleString('en-US'), inline: true }
        ],
        timestamp: new Date().toISOString()
    });
}

function discordLogDisconnect(username, code) {
    sendDiscordWebhook(DISCORD_WEBHOOK_LOGS, null, {
        title:       '🔴 User Disconnected',
        description: `**${username}** left the chat`,
        color:       0x808080,
        fields:      [
            { name: 'Code', value: code, inline: true },
            { name: 'Time', value: new Date().toLocaleString('en-US'), inline: true }
        ],
        timestamp: new Date().toISOString()
    });
}

function discordLogChatMessage(username, compressedMessage) {
    // Decompress before sending to Discord so logs are readable
    const readable = LZString.decompressFromUTF16(compressedMessage) || compressedMessage;
    sendDiscordWebhook(DISCORD_WEBHOOK_CHAT, `**${username}:** ${readable}`);
}

// ─────────────────────────────────────────────
//  Whitelist
// ─────────────────────────────────────────────
const WHITELIST_PATH = path.join(__dirname, 'whitelist.txt');
let whitelist = new Set();
let codeUsage = {};  // { "CODE": ["username1", ...] }

function loadWhitelist() {
    try {
        if (fs.existsSync(WHITELIST_PATH)) {
            const content = fs.readFileSync(WHITELIST_PATH, 'utf8');
            whitelist.clear();
            content.split('\n').forEach(line => {
                const code = line.split('#')[0].trim().toUpperCase();
                if (code.length === CODE_LENGTH) whitelist.add(code);
            });
            console.log(`✅ Whitelist loaded: ${whitelist.size} codes`);
        } else {
            console.log('⚠️  whitelist.txt not found, creating empty file');
            fs.writeFileSync(
                WHITELIST_PATH,
                '# Enter codes here (9 characters)\n# Example: A3K9X7M2B # for Player1\n'
            );
        }
    } catch (error) {
        console.error('❌ Error loading whitelist:', error);
    }
}

function trackCodeUsage(code, username) {
    const upper = code.toUpperCase();
    if (!codeUsage[upper]) codeUsage[upper] = [];
    if (!codeUsage[upper].includes(username)) {
        if (codeUsage[upper].length >= MAX_CODE_USAGE_ENTRIES) {
            codeUsage[upper].shift();
        }
        codeUsage[upper].push(username);
        console.log(`📊 Code ${upper} used by "${username}"`);
    }
}

function isValidCode(code) {
    return whitelist.has(code.toUpperCase());
}

function getActiveSessionsForCode(code) {
    return Array.from(clients.values()).filter(c => c.code === code.toUpperCase() && c.verified);
}

// ─────────────────────────────────────────────
//  State
// ─────────────────────────────────────────────
const clients        = new Map();  // socketId → client object
const messageHistory = new CircularBuffer(MAX_HISTORY);

// Per-socket rate-limit buckets
const verifyAttempts = new Map();  // socketId → { count, resetAt }
const msgAttempts    = new Map();  // socketId → { count, resetAt }

// Per-IP verify rate-limit
const ipVerifyAttempts = new Map();  // ip → { count, resetAt }

function getClientIP(socket) {
    const forwarded = socket.handshake.headers['x-forwarded-for'];
    if (forwarded) return forwarded.split(',')[0].trim();
    return socket.handshake.address;
}

function checkIPVerifyLimit(ip) {
    const now  = Date.now();
    let bucket = ipVerifyAttempts.get(ip);
    if (!bucket || now > bucket.resetAt) {
        bucket = { count: 0, resetAt: now + VERIFY_IP_WINDOW_MS };
        ipVerifyAttempts.set(ip, bucket);
    }
    bucket.count++;
    return bucket.count <= MAX_VERIFY_ATTEMPTS_IP;
}

// Periodic cleanup of expired IP buckets (every 5 minutes)
setInterval(() => {
    const now = Date.now();
    for (const [ip, bucket] of ipVerifyAttempts.entries()) {
        if (now > bucket.resetAt) ipVerifyAttempts.delete(ip);
    }
}, 5 * 60 * 1000);

function broadcastOnlineCount() {
    const verifiedUsers = Array.from(clients.values()).filter(c => c.verified && c.username);
    io.emit('onlineCountUpdate', {
        count: verifiedUsers.length,
        users: verifiedUsers.map(c => c.username)
    });
    console.log(`📊 Online count: ${verifiedUsers.length}`);
}

// ─────────────────────────────────────────────
//  Init
// ─────────────────────────────────────────────
loadWhitelist();

// ─────────────────────────────────────────────
//  HTTP Routes
// ─────────────────────────────────────────────
app.get('/', (req, res) => {
    res.json({
        status:            'Server running',
        time:              new Date().toISOString(),
        connectedClients:  clients.size,
        whitelistedCodes:  whitelist.size,
        discordWebhooksConfigured: {
            logs: !!DISCORD_WEBHOOK_LOGS,
            chat: !!DISCORD_WEBHOOK_CHAT
        }
    });
});

app.get('/reload-whitelist', requireAdminAuth, (req, res) => {
    loadWhitelist();
    res.json({ success: true, message: 'Whitelist reloaded', totalCodes: whitelist.size });
});

app.get('/admin/code-usage', requireAdminAuth, (req, res) => {
    res.json({
        success:    true,
        timestamp:  new Date().toISOString(),
        codeUsage,
        totalCodes: Object.keys(codeUsage).length,
        totalUsers: Object.values(codeUsage).flat().length
    });
});

// ─────────────────────────────────────────────
//  Socket.IO
// ─────────────────────────────────────────────
io.on('connection', (socket) => {
    console.log('🔌 New client connected:', socket.id);

    clients.set(socket.id, {
        id:          socket.id,
        username:    null,
        verified:    false,
        code:        null,
        connectedAt: new Date()
    });

    // Init rate-limit buckets
    verifyAttempts.set(socket.id, { count: 0, resetAt: Date.now() + VERIFY_WINDOW_MS });
    msgAttempts.set(socket.id,    { count: 0, resetAt: Date.now() + MSG_RATE_WINDOW_MS });

    socket.emit('verifyRequired', { message: 'Please verify with /verify CODE' });

    // Auto-kick if still unverified after UNVERIFIED_TIMEOUT_MS
    const unverifiedTimeout = setTimeout(() => {
        const client = clients.get(socket.id);
        if (client && !client.verified) {
            console.log(`⏱️  Kicking unverified socket: ${socket.id}`);
            socket.disconnect();
        }
    }, UNVERIFIED_TIMEOUT_MS);

    // ── Verify Code ──────────────────────────
    socket.on('verifyCode', (data) => {
        // IP-level check first
        const ip = getClientIP(socket);
        if (!checkIPVerifyLimit(ip)) {
            socket.emit('verifyFailed', { message: 'Too many attempts from your network. Try again later.' });
            socket.disconnect();
            return;
        }

        // Socket-level rate limit
        const attempts = verifyAttempts.get(socket.id);
        if (attempts) {
            if (Date.now() > attempts.resetAt) {
                attempts.count   = 0;
                attempts.resetAt = Date.now() + VERIFY_WINDOW_MS;
            }
            attempts.count++;
            if (attempts.count > MAX_VERIFY_ATTEMPTS) {
                socket.emit('verifyFailed', { message: 'Too many attempts. Disconnecting.' });
                socket.disconnect();
                return;
            }
        }

        if (!data || typeof data !== 'object') return;

        const code     = sanitizeString(data.code,     CODE_LENGTH);
        const username = sanitizeString(data.username, MAX_USERNAME_LENGTH);

        if (!code || code.length !== CODE_LENGTH) {
            socket.emit('verifyFailed', { message: `Code must be exactly ${CODE_LENGTH} characters.` });
            return;
        }

        if (!isValidUsername(username)) {
            socket.emit('verifyFailed', {
                message: 'Invalid username. Use letters, numbers, _ or - only (max 32 chars).'
            });
            return;
        }

        const client = clients.get(socket.id);
        if (!client) return;

        const usernameTaken = Array.from(clients.values()).some(
            c => c.verified && c.username === username && c.id !== socket.id
        );
        if (usernameTaken) {
            socket.emit('verifyFailed', { message: 'Username already in use. Pick a different name.' });
            return;
        }

        if (isValidCode(code)) {
            const activeSessions = getActiveSessionsForCode(code);
            if (activeSessions.length >= MAX_SESSIONS_PER_CODE) {
                socket.emit('verifyFailed', {
                    message: `This code is already in use by ${MAX_SESSIONS_PER_CODE} sessions.`
                });
                return;
            }

            clearTimeout(unverifiedTimeout);

            client.verified = true;
            client.code     = code.toUpperCase();
            client.username = username;

            trackCodeUsage(code, username);
            console.log(`✅ ${username} verified with code ${code.toUpperCase()}`);
            discordLogSuccess(username, code.toUpperCase());

            socket.emit('verifySuccess', { message: 'Verification successful! Welcome to the chat.' });

            // Send history + online users list (matches client's 'welcome' handler)
            socket.emit('welcome', {
                history:     messageHistory.toArray(),
                onlineUsers: Array.from(clients.values())
                    .filter(c => c.verified && c.username)
                    .map(c => c.username)
            });

            discordLogConnect(username, code.toUpperCase());

            socket.broadcast.emit('userJoined', {
                username,
                message:   `${username} joined the chat`,
                timestamp: new Date().toISOString()
            });

            broadcastOnlineCount();

        } else {
            console.log(`❌ Invalid code attempt from "${username}": ${code}`);
            discordLogFailed(username, code);
            socket.emit('verifyFailed', { message: 'Code invalid, please try again.' });
        }
    });

    // ── Chat Message ─────────────────────────
    socket.on('chatMessage', (data) => {
        const client = clients.get(socket.id);
        if (!client || !client.verified || !client.username) {
            socket.emit('verifyRequired', { message: 'You must be verified to send messages.' });
            return;
        }

        // Per-socket message rate limiting
        const msgBucket = msgAttempts.get(socket.id);
        if (msgBucket) {
            if (Date.now() > msgBucket.resetAt) {
                msgBucket.count   = 0;
                msgBucket.resetAt = Date.now() + MSG_RATE_WINDOW_MS;
            }
            msgBucket.count++;
            if (msgBucket.count > MSG_RATE_MAX) {
                // 'rateLimited' matches the client-side handler
                socket.emit('rateLimited', { message: 'You are sending messages too fast.' });
                return;
            }
        }

        if (!data || typeof data !== 'object') return;

        // message is LZ-compressed UTF-16 from the client — keep it as-is for relay.
        // We only validate that it is a non-empty string within our byte limit.
        const message = sanitizeString(data.message, MAX_MESSAGE_LENGTH);
        if (!isValidMessage(message)) return;

        const nameColor = isValidHexColor(data.nameColor) ? data.nameColor : '#ffffff';

        // hue: sent by the client as a number (team mode) or undefined/null (other modes)
        const hue = isValidHue(data.hue) ? (data.hue ?? null) : null;

        // realUser: the in-game username displayed next to the chat name.
        // The client reads data.realUser in addChatMessage(), so we must echo it back.
        // We use the verified username stored on the server as the authoritative value.
        const realUser = client.username;

        const msgObj = {
            id:        Date.now() + Math.random(),
            username:  client.username,
            message,               // still LZ-compressed — client decompresses on render
            nameColor,
            hue,                   // number | null
            realUser,              // echoed back so the client can show "(realUser)"
            timestamp: new Date().toISOString(),
            type:      'user'
        };

        messageHistory.push(msgObj);

        // Broadcast to ALL connected sockets (including sender for confirmation)
        io.emit('newMessage', msgObj);

        console.log(`💬 ${msgObj.username}: [compressed message]`);
        discordLogChatMessage(msgObj.username, msgObj.message);
    });

    // ── Disconnect ───────────────────────────
    socket.on('disconnect', () => {
        clearTimeout(unverifiedTimeout);
        const client = clients.get(socket.id);
        verifyAttempts.delete(socket.id);
        msgAttempts.delete(socket.id);

        if (client && client.verified && client.username) {
            console.log(`🔌 Disconnected: ${client.username} (Code: ${client.code})`);
            discordLogDisconnect(client.username, client.code);
            socket.broadcast.emit('userLeft', {
                username:  client.username,
                message:   `${client.username} left the chat`,
                timestamp: new Date().toISOString()
            });
            clients.delete(socket.id);
            broadcastOnlineCount();
        } else {
            console.log(`🔌 Unverified client disconnected: ${socket.id}`);
            clients.delete(socket.id);
        }
    });
});

// ─────────────────────────────────────────────
//  Start
// ─────────────────────────────────────────────
const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
    console.log(`🚀 Server running on port ${PORT}`);
    console.log(`📋 Whitelist: ${whitelist.size} codes loaded`);
    console.log(`🌐 CORS origin: ${ALLOWED_ORIGIN}`);
    console.log(`🔒 Admin auth: ${ADMIN_SECRET ? '✅ Configured' : '❌ ADMIN_SECRET not set – admin routes unprotected!'}`);
    console.log(`🔔 Discord: ${DISCORD_WEBHOOK_LOGS ? '✅' : '❌'} Logs | ${DISCORD_WEBHOOK_CHAT ? '✅' : '❌'} Chat`);
});
