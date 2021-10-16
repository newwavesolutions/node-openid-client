"use strict";

function asyncGeneratorStep(gen, resolve, reject, _next, _throw, key, arg) { try { var info = gen[key](arg); var value = info.value; } catch (error) { reject(error); return; } if (info.done) { resolve(value); } else { Promise.resolve(value).then(_next, _throw); } }

function _asyncToGenerator(fn) { return function () { var self = this, args = arguments; return new Promise(function (resolve, reject) { var gen = fn.apply(self, args); function _next(value) { asyncGeneratorStep(gen, resolve, reject, _next, _throw, "next", value); } function _throw(err) { asyncGeneratorStep(gen, resolve, reject, _next, _throw, "throw", err); } _next(undefined); }); }; }

/* eslint-disable max-classes-per-file */
const {
  inspect,
  deprecate
} = require('util');

const stdhttp = require('http');

const crypto = require('crypto');

const {
  strict: assert
} = require('assert');

const querystring = require('querystring');

const url = require('url');

const {
  ParseError
} = require('got');

const jose = require('jose');

const base64url = require('base64url');

const tokenHash = require('oidc-token-hash');

const defaults = require('./helpers/defaults');

const {
  assertSigningAlgValuesSupport,
  assertIssuerConfiguration
} = require('./helpers/assert');

const pick = require('./helpers/pick');

const isPlainObject = require('./helpers/is_plain_object');

const processResponse = require('./helpers/process_response');

const TokenSet = require('./token_set');

const {
  OPError,
  RPError
} = require('./errors');

const now = require('./helpers/unix_timestamp');

const {
  random
} = require('./helpers/generators');

const request = require('./helpers/request');

const {
  CALLBACK_PROPERTIES,
  CLIENT_DEFAULTS,
  JWT_CONTENT,
  CLOCK_TOLERANCE
} = require('./helpers/consts');

const issuerRegistry = require('./issuer_registry');

const instance = require('./helpers/weak_cache');

const {
  authenticatedPost,
  resolveResponseType,
  resolveRedirectUri
} = require('./helpers/client');

const DeviceFlowHandle = require('./device_flow_handle');

const {
  deep: defaultsDeep
} = defaults;

function pickCb(input) {
  return pick(input, ...CALLBACK_PROPERTIES);
}

function authorizationHeaderValue(token, tokenType = 'Bearer') {
  return `${tokenType} ${token}`;
}

function cleanUpClaims(claims) {
  if (Object.keys(claims._claim_names).length === 0) {
    delete claims._claim_names;
  }

  if (Object.keys(claims._claim_sources).length === 0) {
    delete claims._claim_sources;
  }
}

function assignClaim(target, source, sourceName, throwOnMissing = true) {
  return ([claim, inSource]) => {
    if (inSource === sourceName) {
      if (throwOnMissing && source[claim] === undefined) {
        throw new RPError(`expected claim "${claim}" in "${sourceName}"`);
      } else if (source[claim] !== undefined) {
        target[claim] = source[claim];
      }

      delete target._claim_names[claim];
    }
  };
}

function verifyPresence(payload, jwt, prop) {
  if (payload[prop] === undefined) {
    throw new RPError({
      message: `missing required JWT property ${prop}`,
      jwt
    });
  }
}

function authorizationParams(params) {
  const authParams = {
    client_id: this.client_id,
    scope: 'openid',
    response_type: resolveResponseType.call(this),
    redirect_uri: resolveRedirectUri.call(this),
    ...params
  };
  Object.entries(authParams).forEach(([key, value]) => {
    if (value === null || value === undefined) {
      delete authParams[key];
    } else if (key === 'claims' && typeof value === 'object') {
      authParams[key] = JSON.stringify(value);
    } else if (key === 'resource' && Array.isArray(value)) {
      authParams[key] = value;
    } else if (typeof value !== 'string') {
      authParams[key] = String(value);
    }
  });
  return authParams;
}

function claimJWT(_x, _x2) {
  return _claimJWT.apply(this, arguments);
}

function _claimJWT() {
  _claimJWT = _asyncToGenerator(function* (label, jwt) {
    try {
      const {
        header,
        payload
      } = jose.JWT.decode(jwt, {
        complete: true
      });
      const {
        iss
      } = payload;

      if (header.alg === 'none') {
        return payload;
      }

      let key;

      if (!iss || iss === this.issuer.issuer) {
        key = yield this.issuer.queryKeyStore(header);
      } else if (issuerRegistry.has(iss)) {
        key = yield issuerRegistry.get(iss).queryKeyStore(header);
      } else {
        const discovered = yield this.issuer.constructor.discover(iss);
        key = yield discovered.queryKeyStore(header);
      }

      return jose.JWT.verify(jwt, key);
    } catch (err) {
      if (err instanceof RPError || err instanceof OPError || err.name === 'AggregateError') {
        throw err;
      } else {
        throw new RPError({
          printf: ['failed to validate the %s JWT (%s: %s)', label, err.name, err.message],
          jwt
        });
      }
    }
  });
  return _claimJWT.apply(this, arguments);
}

function getKeystore(jwks) {
  const keystore = jose.JWKS.asKeyStore(jwks);

  if (keystore.all().some(key => key.type !== 'private')) {
    throw new TypeError('jwks must only contain private keys');
  }

  return keystore;
} // if an OP doesnt support client_secret_basic but supports client_secret_post, use it instead
// this is in place to take care of most common pitfalls when first using discovered Issuers without
// the support for default values defined by Discovery 1.0


function checkBasicSupport(client, metadata, properties) {
  try {
    const supported = client.issuer.token_endpoint_auth_methods_supported;

    if (!supported.includes(properties.token_endpoint_auth_method)) {
      if (supported.includes('client_secret_post')) {
        properties.token_endpoint_auth_method = 'client_secret_post';
      }
    }
  } catch (err) {}
}

function handleCommonMistakes(client, metadata, properties) {
  if (!metadata.token_endpoint_auth_method) {
    // if no explicit value was provided
    checkBasicSupport(client, metadata, properties);
  } // :fp: c'mon people... RTFM


  if (metadata.redirect_uri) {
    if (metadata.redirect_uris) {
      throw new TypeError('provide a redirect_uri or redirect_uris, not both');
    }

    properties.redirect_uris = [metadata.redirect_uri];
    delete properties.redirect_uri;
  }

  if (metadata.response_type) {
    if (metadata.response_types) {
      throw new TypeError('provide a response_type or response_types, not both');
    }

    properties.response_types = [metadata.response_type];
    delete properties.response_type;
  }
}

function getDefaultsForEndpoint(endpoint, issuer, properties) {
  if (!issuer[`${endpoint}_endpoint`]) return;
  const tokenEndpointAuthMethod = properties.token_endpoint_auth_method;
  const tokenEndpointAuthSigningAlg = properties.token_endpoint_auth_signing_alg;
  const eam = `${endpoint}_endpoint_auth_method`;
  const easa = `${endpoint}_endpoint_auth_signing_alg`;

  if (properties[eam] === undefined && properties[easa] === undefined) {
    if (tokenEndpointAuthMethod !== undefined) {
      properties[eam] = tokenEndpointAuthMethod;
    }

    if (tokenEndpointAuthSigningAlg !== undefined) {
      properties[easa] = tokenEndpointAuthSigningAlg;
    }
  }
}

class BaseClient {}

module.exports = (issuer, aadIssValidation = false) => class Client extends BaseClient {
  /**
   * @name constructor
   * @api public
   */
  constructor(metadata = {}, jwks, options) {
    super();

    if (typeof metadata.client_id !== 'string' || !metadata.client_id) {
      throw new TypeError('client_id is required');
    }

    const properties = { ...CLIENT_DEFAULTS,
      ...metadata
    };
    handleCommonMistakes(this, metadata, properties);
    assertSigningAlgValuesSupport('token', this.issuer, properties);
    ['introspection', 'revocation'].forEach(endpoint => {
      getDefaultsForEndpoint(endpoint, this.issuer, properties);
      assertSigningAlgValuesSupport(endpoint, this.issuer, properties);
    });
    Object.entries(properties).forEach(([key, value]) => {
      instance(this).get('metadata').set(key, value);

      if (!this[key]) {
        Object.defineProperty(this, key, {
          get() {
            return instance(this).get('metadata').get(key);
          },

          enumerable: true
        });
      }
    });

    if (jwks !== undefined) {
      const keystore = getKeystore.call(this, jwks);
      instance(this).set('keystore', keystore);
    }

    if (options !== undefined) {
      instance(this).set('options', options);
    }

    this[CLOCK_TOLERANCE] = 0;
  }
  /**
   * @name authorizationUrl
   * @api public
   */


  authorizationUrl(params = {}) {
    if (!isPlainObject(params)) {
      throw new TypeError('params must be a plain object');
    }

    assertIssuerConfiguration(this.issuer, 'authorization_endpoint');
    const target = url.parse(this.issuer.authorization_endpoint, true);
    target.search = null;
    target.query = { ...target.query,
      ...authorizationParams.call(this, params)
    };
    return url.format(target);
  }
  /**
   * @name authorizationPost
   * @api public
   */


  authorizationPost(params = {}) {
    if (!isPlainObject(params)) {
      throw new TypeError('params must be a plain object');
    }

    const inputs = authorizationParams.call(this, params);
    const formInputs = Object.keys(inputs).map(name => `<input type="hidden" name="${name}" value="${inputs[name]}"/>`).join('\n');
    return `<!DOCTYPE html>
<head>
  <title>Requesting Authorization</title>
</head>
<body onload="javascript:document.forms[0].submit()">
  <form method="post" action="${this.issuer.authorization_endpoint}">
    ${formInputs}
  </form>
</body>
</html>`;
  }
  /**
   * @name endSessionUrl
   * @api public
   */


  endSessionUrl(params = {}) {
    assertIssuerConfiguration(this.issuer, 'end_session_endpoint');
    const {
      0: postLogout,
      length
    } = this.post_logout_redirect_uris || [];
    const {
      post_logout_redirect_uri = length === 1 ? postLogout : undefined
    } = params;
    let hint = params.id_token_hint;

    if (hint instanceof TokenSet) {
      if (!hint.id_token) {
        throw new TypeError('id_token not present in TokenSet');
      }

      hint = hint.id_token;
    }

    const target = url.parse(this.issuer.end_session_endpoint, true);
    target.search = null;
    target.query = { ...params,
      ...target.query,
      ...{
        post_logout_redirect_uri,
        id_token_hint: hint
      }
    };
    Object.entries(target.query).forEach(([key, value]) => {
      if (value === null || value === undefined) {
        delete target.query[key];
      }
    });
    return url.format(target);
  }
  /**
   * @name callbackParams
   * @api public
   */


  callbackParams(input) {
    // eslint-disable-line class-methods-use-this
    const isIncomingMessage = input instanceof stdhttp.IncomingMessage || input && input.method && input.url;
    const isString = typeof input === 'string';

    if (!isString && !isIncomingMessage) {
      throw new TypeError('#callbackParams only accepts string urls, http.IncomingMessage or a lookalike');
    }

    if (isIncomingMessage) {
      switch (input.method) {
        case 'GET':
          return pickCb(url.parse(input.url, true).query);

        case 'POST':
          if (input.body === undefined) {
            throw new TypeError('incoming message body missing, include a body parser prior to this method call');
          }

          switch (typeof input.body) {
            case 'object':
            case 'string':
              if (Buffer.isBuffer(input.body)) {
                return pickCb(querystring.parse(input.body.toString('utf-8')));
              }

              if (typeof input.body === 'string') {
                return pickCb(querystring.parse(input.body));
              }

              return pickCb(input.body);

            default:
              throw new TypeError('invalid IncomingMessage body object');
          }

        default:
          throw new TypeError('invalid IncomingMessage method');
      }
    } else {
      return pickCb(url.parse(input, true).query);
    }
  }
  /**
   * @name callback
   * @api public
   */


  callback(redirectUri, parameters, checks = {}, {
    exchangeBody,
    clientAssertionPayload
  } = {}) {
    var _this = this;

    return _asyncToGenerator(function* () {
      let params = pickCb(parameters);

      if (checks.jarm && !('response' in parameters)) {
        throw new RPError({
          message: 'expected a JARM response',
          checks,
          params
        });
      } else if ('response' in parameters) {
        const decrypted = yield _this.decryptJARM(params.response);
        params = yield _this.validateJARM(decrypted);
      }

      if (_this.default_max_age && !checks.max_age) {
        checks.max_age = _this.default_max_age;
      }

      if (params.state && !checks.state) {
        throw new TypeError('checks.state argument is missing');
      }

      if (!params.state && checks.state) {
        throw new RPError({
          message: 'state missing from the response',
          checks,
          params
        });
      }

      if (checks.state !== params.state) {
        throw new RPError({
          printf: ['state mismatch, expected %s, got: %s', checks.state, params.state],
          checks,
          params
        });
      }

      if (params.error) {
        throw new OPError(params);
      }

      const RESPONSE_TYPE_REQUIRED_PARAMS = {
        code: ['code'],
        id_token: ['id_token'],
        token: ['access_token', 'token_type']
      };

      if (checks.response_type) {
        for (const type of checks.response_type.split(' ')) {
          // eslint-disable-line no-restricted-syntax
          if (type === 'none') {
            if (params.code || params.id_token || params.access_token) {
              throw new RPError({
                message: 'unexpected params encountered for "none" response',
                checks,
                params
              });
            }
          } else {
            for (const param of RESPONSE_TYPE_REQUIRED_PARAMS[type]) {
              // eslint-disable-line no-restricted-syntax, max-len
              if (!params[param]) {
                throw new RPError({
                  message: `${param} missing from response`,
                  checks,
                  params
                });
              }
            }
          }
        }
      }

      if (params.id_token) {
        const tokenset = new TokenSet(params);
        yield _this.decryptIdToken(tokenset);
        yield _this.validateIdToken(tokenset, checks.nonce, 'authorization', checks.max_age, checks.state);

        if (!params.code) {
          return tokenset;
        }
      }

      if (params.code) {
        const tokenset = yield _this.grant({ ...exchangeBody,
          grant_type: 'authorization_code',
          code: params.code,
          redirect_uri: redirectUri,
          code_verifier: checks.code_verifier
        }, {
          clientAssertionPayload
        });
        yield _this.decryptIdToken(tokenset);
        yield _this.validateIdToken(tokenset, checks.nonce, 'token', checks.max_age);

        if (params.session_state) {
          tokenset.session_state = params.session_state;
        }

        return tokenset;
      }

      return new TokenSet(params);
    })();
  }
  /**
   * @name oauthCallback
   * @api public
   */


  oauthCallback(redirectUri, parameters, checks = {}, {
    exchangeBody,
    clientAssertionPayload
  } = {}) {
    var _this2 = this;

    return _asyncToGenerator(function* () {
      let params = pickCb(parameters);

      if (checks.jarm && !('response' in parameters)) {
        throw new RPError({
          message: 'expected a JARM response',
          checks,
          params
        });
      } else if ('response' in parameters) {
        const decrypted = yield _this2.decryptJARM(params.response);
        params = yield _this2.validateJARM(decrypted);
      }

      if (params.state && !checks.state) {
        throw new TypeError('checks.state argument is missing');
      }

      if (!params.state && checks.state) {
        throw new RPError({
          message: 'state missing from the response',
          checks,
          params
        });
      }

      if (checks.state !== params.state) {
        throw new RPError({
          printf: ['state mismatch, expected %s, got: %s', checks.state, params.state],
          checks,
          params
        });
      }

      if (params.error) {
        throw new OPError(params);
      }

      const RESPONSE_TYPE_REQUIRED_PARAMS = {
        code: ['code'],
        token: ['access_token', 'token_type']
      };

      if (checks.response_type) {
        for (const type of checks.response_type.split(' ')) {
          // eslint-disable-line no-restricted-syntax
          if (type === 'none') {
            if (params.code || params.id_token || params.access_token) {
              throw new RPError({
                message: 'unexpected params encountered for "none" response',
                checks,
                params
              });
            }
          }

          if (RESPONSE_TYPE_REQUIRED_PARAMS[type]) {
            for (const param of RESPONSE_TYPE_REQUIRED_PARAMS[type]) {
              // eslint-disable-line no-restricted-syntax, max-len
              if (!params[param]) {
                throw new RPError({
                  message: `${param} missing from response`,
                  checks,
                  params
                });
              }
            }
          }
        }
      }

      if (params.code) {
        return _this2.grant({ ...exchangeBody,
          grant_type: 'authorization_code',
          code: params.code,
          redirect_uri: redirectUri,
          code_verifier: checks.code_verifier
        }, {
          clientAssertionPayload
        });
      }

      return new TokenSet(params);
    })();
  }
  /**
   * @name decryptIdToken
   * @api private
   */


  decryptIdToken(token) {
    var _this3 = this;

    return _asyncToGenerator(function* () {
      if (!_this3.id_token_encrypted_response_alg) {
        return token;
      }

      let idToken = token;

      if (idToken instanceof TokenSet) {
        if (!idToken.id_token) {
          throw new TypeError('id_token not present in TokenSet');
        }

        idToken = idToken.id_token;
      }

      const expectedAlg = _this3.id_token_encrypted_response_alg;
      const expectedEnc = _this3.id_token_encrypted_response_enc;
      const result = yield _this3.decryptJWE(idToken, expectedAlg, expectedEnc);

      if (token instanceof TokenSet) {
        token.id_token = result;
        return token;
      }

      return result;
    })();
  }

  validateJWTUserinfo(body) {
    var _this4 = this;

    return _asyncToGenerator(function* () {
      const expectedAlg = _this4.userinfo_signed_response_alg;
      return _this4.validateJWT(body, expectedAlg, []);
    })();
  }
  /**
   * @name decryptJARM
   * @api private
   */


  decryptJARM(response) {
    var _this5 = this;

    return _asyncToGenerator(function* () {
      if (!_this5.authorization_encrypted_response_alg) {
        return response;
      }

      const expectedAlg = _this5.authorization_encrypted_response_alg;
      const expectedEnc = _this5.authorization_encrypted_response_enc;
      return _this5.decryptJWE(response, expectedAlg, expectedEnc);
    })();
  }
  /**
   * @name validateJARM
   * @api private
   */


  validateJARM(response) {
    var _this6 = this;

    return _asyncToGenerator(function* () {
      const expectedAlg = _this6.authorization_signed_response_alg;
      const {
        payload
      } = yield _this6.validateJWT(response, expectedAlg, ['iss', 'exp', 'aud']);
      return pickCb(payload);
    })();
  }
  /**
   * @name decryptJWTUserinfo
   * @api private
   */


  decryptJWTUserinfo(body) {
    var _this7 = this;

    return _asyncToGenerator(function* () {
      if (!_this7.userinfo_encrypted_response_alg) {
        return body;
      }

      const expectedAlg = _this7.userinfo_encrypted_response_alg;
      const expectedEnc = _this7.userinfo_encrypted_response_enc;
      return _this7.decryptJWE(body, expectedAlg, expectedEnc);
    })();
  }
  /**
   * @name decryptJWE
   * @api private
   */


  decryptJWE(jwe, expectedAlg, expectedEnc = 'A128CBC-HS256') {
    var _this8 = this;

    return _asyncToGenerator(function* () {
      const header = JSON.parse(base64url.decode(jwe.split('.')[0]));

      if (header.alg !== expectedAlg) {
        throw new RPError({
          printf: ['unexpected JWE alg received, expected %s, got: %s', expectedAlg, header.alg],
          jwt: jwe
        });
      }

      if (header.enc !== expectedEnc) {
        throw new RPError({
          printf: ['unexpected JWE enc received, expected %s, got: %s', expectedEnc, header.enc],
          jwt: jwe
        });
      }

      let keyOrStore;

      if (expectedAlg.match(/^(?:RSA|ECDH)/)) {
        keyOrStore = instance(_this8).get('keystore');
      } else {
        keyOrStore = yield _this8.joseSecret(expectedAlg === 'dir' ? expectedEnc : expectedAlg);
      }

      const payload = jose.JWE.decrypt(jwe, keyOrStore);
      return payload.toString('utf8');
    })();
  }
  /**
   * @name validateIdToken
   * @api private
   */


  validateIdToken(tokenSet, nonce, returnedBy, maxAge, state) {
    var _this9 = this;

    return _asyncToGenerator(function* () {
      let idToken = tokenSet;
      const expectedAlg = _this9.id_token_signed_response_alg;
      const isTokenSet = idToken instanceof TokenSet;

      if (isTokenSet) {
        if (!idToken.id_token) {
          throw new TypeError('id_token not present in TokenSet');
        }

        idToken = idToken.id_token;
      }

      idToken = String(idToken);
      const timestamp = now();
      const {
        protected: header,
        payload,
        key
      } = yield _this9.validateJWT(idToken, expectedAlg);

      if (maxAge || maxAge !== null && _this9.require_auth_time) {
        if (!payload.auth_time) {
          throw new RPError({
            message: 'missing required JWT property auth_time',
            jwt: idToken
          });
        }

        if (typeof payload.auth_time !== 'number') {
          throw new RPError({
            message: 'JWT auth_time claim must be a JSON numeric value',
            jwt: idToken
          });
        }
      }

      if (maxAge && payload.auth_time + maxAge < timestamp - _this9[CLOCK_TOLERANCE]) {
        throw new RPError({
          printf: ['too much time has elapsed since the last End-User authentication, max_age %i, auth_time: %i, now %i', maxAge, payload.auth_time, timestamp - _this9[CLOCK_TOLERANCE]],
          now: timestamp,
          tolerance: _this9[CLOCK_TOLERANCE],
          auth_time: payload.auth_time,
          jwt: idToken
        });
      }

      if (nonce !== null && (payload.nonce || nonce !== undefined) && payload.nonce !== nonce) {
        throw new RPError({
          printf: ['nonce mismatch, expected %s, got: %s', nonce, payload.nonce],
          jwt: idToken
        });
      }

      if (returnedBy === 'authorization') {
        if (!payload.at_hash && tokenSet.access_token) {
          throw new RPError({
            message: 'missing required property at_hash',
            jwt: idToken
          });
        }

        if (!payload.c_hash && tokenSet.code) {
          throw new RPError({
            message: 'missing required property c_hash',
            jwt: idToken
          });
        }

        const fapi = _this9.constructor.name === 'FAPIClient';

        if (fapi) {
          if (payload.iat < timestamp - 3600) {
            throw new RPError({
              printf: ['JWT issued too far in the past, now %i, iat %i', timestamp, payload.iat],
              now: timestamp,
              tolerance: _this9[CLOCK_TOLERANCE],
              iat: payload.iat,
              jwt: idToken
            });
          }

          if (!payload.s_hash && (tokenSet.state || state)) {
            throw new RPError({
              message: 'missing required property s_hash',
              jwt: idToken
            });
          }
        }

        if (payload.s_hash) {
          if (!state) {
            throw new TypeError('cannot verify s_hash, "checks.state" property not provided');
          }

          try {
            tokenHash.validate({
              claim: 's_hash',
              source: 'state'
            }, payload.s_hash, state, header.alg, key && key.crv);
          } catch (err) {
            throw new RPError({
              message: err.message,
              jwt: idToken
            });
          }
        }
      }

      if (tokenSet.access_token && payload.at_hash !== undefined) {
        try {
          tokenHash.validate({
            claim: 'at_hash',
            source: 'access_token'
          }, payload.at_hash, tokenSet.access_token, header.alg, key && key.crv);
        } catch (err) {
          throw new RPError({
            message: err.message,
            jwt: idToken
          });
        }
      }

      if (tokenSet.code && payload.c_hash !== undefined) {
        try {
          tokenHash.validate({
            claim: 'c_hash',
            source: 'code'
          }, payload.c_hash, tokenSet.code, header.alg, key && key.crv);
        } catch (err) {
          throw new RPError({
            message: err.message,
            jwt: idToken
          });
        }
      }

      return tokenSet;
    })();
  }
  /**
   * @name validateJWT
   * @api private
   */


  validateJWT(jwt, expectedAlg, required = ['iss', 'sub', 'aud', 'exp', 'iat']) {
    var _this10 = this;

    return _asyncToGenerator(function* () {
      const isSelfIssued = _this10.issuer.issuer === 'https://self-issued.me';
      const timestamp = now();
      let header;
      let payload;

      try {
        ({
          header,
          payload
        } = jose.JWT.decode(jwt, {
          complete: true
        }));
      } catch (err) {
        throw new RPError({
          printf: ['failed to decode JWT (%s: %s)', err.name, err.message],
          jwt
        });
      }

      if (header.alg !== expectedAlg) {
        throw new RPError({
          printf: ['unexpected JWT alg received, expected %s, got: %s', expectedAlg, header.alg],
          jwt
        });
      }

      if (isSelfIssued) {
        required = [...required, 'sub_jwk']; // eslint-disable-line no-param-reassign
      }

      required.forEach(verifyPresence.bind(undefined, payload, jwt));

      if (payload.iss !== undefined) {
        let expectedIss = _this10.issuer.issuer;

        if (aadIssValidation) {
          expectedIss = _this10.issuer.issuer.replace('{tenantid}', payload.tid);
        }

        if (payload.iss !== expectedIss) {
          throw new RPError({
            printf: ['unexpected iss value, expected %s, got: %s', expectedIss, payload.iss],
            jwt
          });
        }
      }

      if (payload.iat !== undefined) {
        if (typeof payload.iat !== 'number') {
          throw new RPError({
            message: 'JWT iat claim must be a JSON numeric value',
            jwt
          });
        }
      }

      if (payload.nbf !== undefined) {
        if (typeof payload.nbf !== 'number') {
          throw new RPError({
            message: 'JWT nbf claim must be a JSON numeric value',
            jwt
          });
        }

        if (payload.nbf > timestamp + _this10[CLOCK_TOLERANCE]) {
          throw new RPError({
            printf: ['JWT not active yet, now %i, nbf %i', timestamp + _this10[CLOCK_TOLERANCE], payload.nbf],
            now: timestamp,
            tolerance: _this10[CLOCK_TOLERANCE],
            nbf: payload.nbf,
            jwt
          });
        }
      }

      if (payload.exp !== undefined) {
        if (typeof payload.exp !== 'number') {
          throw new RPError({
            message: 'JWT exp claim must be a JSON numeric value',
            jwt
          });
        }

        if (timestamp - _this10[CLOCK_TOLERANCE] >= payload.exp) {
          throw new RPError({
            printf: ['JWT expired, now %i, exp %i', timestamp - _this10[CLOCK_TOLERANCE], payload.exp],
            now: timestamp,
            tolerance: _this10[CLOCK_TOLERANCE],
            exp: payload.exp,
            jwt
          });
        }
      }

      if (payload.aud !== undefined) {
        if (Array.isArray(payload.aud)) {
          if (payload.aud.length > 1 && !payload.azp) {
            throw new RPError({
              message: 'missing required JWT property azp',
              jwt
            });
          }

          if (!payload.aud.includes(_this10.client_id)) {
            throw new RPError({
              printf: ['aud is missing the client_id, expected %s to be included in %j', _this10.client_id, payload.aud],
              jwt
            });
          }
        } else if (payload.aud !== _this10.client_id) {
          throw new RPError({
            printf: ['aud mismatch, expected %s, got: %s', _this10.client_id, payload.aud],
            jwt
          });
        }
      }

      if (payload.azp !== undefined) {
        let {
          additionalAuthorizedParties
        } = instance(_this10).get('options') || {};

        if (typeof additionalAuthorizedParties === 'string') {
          additionalAuthorizedParties = [_this10.client_id, additionalAuthorizedParties];
        } else if (Array.isArray(additionalAuthorizedParties)) {
          additionalAuthorizedParties = [_this10.client_id, ...additionalAuthorizedParties];
        } else {
          additionalAuthorizedParties = [_this10.client_id];
        }

        if (!additionalAuthorizedParties.includes(payload.azp)) {
          throw new RPError({
            printf: ['azp mismatch, got: %s', payload.azp],
            jwt
          });
        }
      }

      let key;

      if (isSelfIssued) {
        try {
          assert(isPlainObject(payload.sub_jwk));
          key = jose.JWK.asKey(payload.sub_jwk);
          assert.equal(key.type, 'public');
        } catch (err) {
          throw new RPError({
            message: 'failed to use sub_jwk claim as an asymmetric JSON Web Key',
            jwt
          });
        }

        if (key.thumbprint !== payload.sub) {
          throw new RPError({
            message: 'failed to match the subject with sub_jwk',
            jwt
          });
        }
      } else if (header.alg.startsWith('HS')) {
        key = yield _this10.joseSecret();
      } else if (header.alg !== 'none') {
        key = yield _this10.issuer.queryKeyStore(header);
      }

      if (!key && header.alg === 'none') {
        return {
          protected: header,
          payload
        };
      }

      try {
        return jose.JWS.verify(jwt, key, {
          complete: true
        });
      } catch (err) {
        throw new RPError({
          message: 'failed to validate JWT signature',
          jwt
        });
      }
    })();
  }
  /**
   * @name refresh
   * @api public
   */


  refresh(refreshToken, {
    exchangeBody,
    clientAssertionPayload
  } = {}) {
    var _this11 = this;

    return _asyncToGenerator(function* () {
      let token = refreshToken;

      if (token instanceof TokenSet) {
        if (!token.refresh_token) {
          throw new TypeError('refresh_token not present in TokenSet');
        }

        token = token.refresh_token;
      }

      const tokenset = yield _this11.grant({ ...exchangeBody,
        grant_type: 'refresh_token',
        refresh_token: String(token)
      }, {
        clientAssertionPayload
      });

      if (tokenset.id_token) {
        yield _this11.decryptIdToken(tokenset);
        yield _this11.validateIdToken(tokenset, null, 'token', null);

        if (refreshToken instanceof TokenSet && refreshToken.id_token) {
          const expectedSub = refreshToken.claims().sub;
          const actualSub = tokenset.claims().sub;

          if (actualSub !== expectedSub) {
            throw new RPError({
              printf: ['sub mismatch, expected %s, got: %s', expectedSub, actualSub],
              jwt: tokenset.id_token
            });
          }
        }
      }

      return tokenset;
    })();
  }

  requestResource(resourceUrl, accessToken, {
    method,
    headers,
    body,
    tokenType = accessToken instanceof TokenSet ? accessToken.token_type : 'Bearer'
  } = {}) {
    var _this12 = this;

    return _asyncToGenerator(function* () {
      if (accessToken instanceof TokenSet) {
        if (!accessToken.access_token) {
          throw new TypeError('access_token not present in TokenSet');
        }

        accessToken = accessToken.access_token; // eslint-disable-line no-param-reassign
      }

      const requestOpts = {
        headers: {
          Authorization: authorizationHeaderValue(accessToken, tokenType),
          ...headers
        },
        body
      };
      const mTLS = !!_this12.tls_client_certificate_bound_access_tokens;
      return request.call(_this12, { ...requestOpts,
        encoding: null,
        method,
        url: resourceUrl
      }, {
        mTLS
      });
    })();
  }
  /**
   * @name userinfo
   * @api public
   */


  userinfo(accessToken, {
    verb = 'GET',
    via = 'header',
    tokenType,
    params
  } = {}) {
    var _this13 = this;

    return _asyncToGenerator(function* () {
      // TODO: in v4.x remove verb in favour of method
      assertIssuerConfiguration(_this13.issuer, 'userinfo_endpoint');
      const options = {
        tokenType,
        method: String(verb).toUpperCase()
      };

      if (options.method !== 'GET' && options.method !== 'POST') {
        throw new TypeError('#userinfo() verb can only be POST or a GET');
      }

      if (via === 'query' && options.method !== 'GET') {
        throw new TypeError('userinfo endpoints will only parse query strings for GET requests');
      } else if (via === 'body' && options.method !== 'POST') {
        throw new TypeError('can only send body on POST');
      }

      const jwt = !!(_this13.userinfo_signed_response_alg || _this13.userinfo_encrypted_response_alg);

      if (jwt) {
        options.headers = {
          Accept: 'application/jwt'
        };
      } else {
        options.headers = {
          Accept: 'application/json'
        };
      }

      const mTLS = !!_this13.tls_client_certificate_bound_access_tokens;
      let targetUrl;

      if (mTLS && _this13.issuer.mtls_endpoint_aliases) {
        targetUrl = _this13.issuer.mtls_endpoint_aliases.userinfo_endpoint;
      }

      targetUrl = new url.URL(targetUrl || _this13.issuer.userinfo_endpoint); // when via is not header we clear the Authorization header and add either
      // query string parameters or urlencoded body access_token parameter

      if (via === 'query') {
        options.headers.Authorization = undefined;
        targetUrl.searchParams.append('access_token', accessToken instanceof TokenSet ? accessToken.access_token : accessToken);
      } else if (via === 'body') {
        options.headers.Authorization = undefined;
        options.headers['Content-Type'] = 'application/x-www-form-urlencoded';
        options.body = new url.URLSearchParams();
        options.body.append('access_token', accessToken instanceof TokenSet ? accessToken.access_token : accessToken);
      } // handle additional parameters, GET via querystring, POST via urlencoded body


      if (params) {
        if (options.method === 'GET') {
          Object.entries(params).forEach(([key, value]) => {
            targetUrl.searchParams.append(key, value);
          });
        } else if (options.body) {
          // POST && via body
          Object.entries(params).forEach(([key, value]) => {
            options.body.append(key, value);
          });
        } else {
          // POST && via header
          options.body = new url.URLSearchParams();
          options.headers['Content-Type'] = 'application/x-www-form-urlencoded';
          Object.entries(params).forEach(([key, value]) => {
            options.body.append(key, value);
          });
        }
      }

      if (options.body) {
        options.body = options.body.toString();
      }

      const response = yield _this13.requestResource(targetUrl, accessToken, options);
      let parsed = processResponse(response, {
        bearer: true
      });

      if (jwt) {
        if (!JWT_CONTENT.test(response.headers['content-type'])) {
          throw new RPError({
            message: 'expected application/jwt response from the userinfo_endpoint',
            response
          });
        }

        const body = response.body.toString();
        const userinfo = yield _this13.decryptJWTUserinfo(body);

        if (!_this13.userinfo_signed_response_alg) {
          try {
            parsed = JSON.parse(userinfo);
            assert(isPlainObject(parsed));
          } catch (err) {
            throw new RPError({
              message: 'failed to parse userinfo JWE payload as JSON',
              jwt: userinfo
            });
          }
        } else {
          ({
            payload: parsed
          } = yield _this13.validateJWTUserinfo(userinfo));
        }
      } else {
        try {
          parsed = JSON.parse(response.body);
        } catch (error) {
          const parseError = new ParseError(error, response.statusCode, response.request.gotOptions, response.body);
          Object.defineProperty(parseError, 'response', {
            value: response
          });
          throw parseError;
        }
      }

      if (accessToken instanceof TokenSet && accessToken.id_token) {
        const expectedSub = accessToken.claims().sub;

        if (parsed.sub !== expectedSub) {
          throw new RPError({
            printf: ['userinfo sub mismatch, expected %s, got: %s', expectedSub, parsed.sub],
            body: parsed,
            jwt: accessToken.id_token
          });
        }
      }

      return parsed;
    })();
  }
  /**
   * @name derivedKey
   * @api private
   */


  derivedKey(len) {
    var _this14 = this;

    return _asyncToGenerator(function* () {
      const cacheKey = `${len}_key`;

      if (instance(_this14).has(cacheKey)) {
        return instance(_this14).get(cacheKey);
      }

      const hash = len <= 256 ? 'sha256' : len <= 384 ? 'sha384' : len <= 512 ? 'sha512' : false; // eslint-disable-line no-nested-ternary

      if (!hash) {
        throw new Error('unsupported symmetric encryption key derivation');
      }

      const derivedBuffer = crypto.createHash(hash).update(_this14.client_secret).digest().slice(0, len / 8);
      const key = jose.JWK.asKey({
        k: base64url.encode(derivedBuffer),
        kty: 'oct'
      });
      instance(_this14).set(cacheKey, key);
      return key;
    })();
  }
  /**
   * @name joseSecret
   * @api private
   */


  joseSecret(alg) {
    var _this15 = this;

    return _asyncToGenerator(function* () {
      if (!_this15.client_secret) {
        throw new TypeError('client_secret is required');
      }

      if (/^A(\d{3})(?:GCM)?KW$/.test(alg)) {
        return _this15.derivedKey(parseInt(RegExp.$1, 10));
      }

      if (/^A(\d{3})(?:GCM|CBC-HS(\d{3}))$/.test(alg)) {
        return _this15.derivedKey(parseInt(RegExp.$2 || RegExp.$1, 10));
      }

      if (instance(_this15).has('jose_secret')) {
        return instance(_this15).get('jose_secret');
      }

      const key = jose.JWK.asKey({
        k: base64url.encode(_this15.client_secret),
        kty: 'oct'
      });
      instance(_this15).set('jose_secret', key);
      return key;
    })();
  }
  /**
   * @name grant
   * @api public
   */


  grant(body, {
    clientAssertionPayload
  } = {}) {
    var _this16 = this;

    return _asyncToGenerator(function* () {
      assertIssuerConfiguration(_this16.issuer, 'token_endpoint');
      const response = yield authenticatedPost.call(_this16, 'token', {
        form: true,
        body,
        json: true
      }, {
        clientAssertionPayload
      });
      const responseBody = processResponse(response);
      return new TokenSet(responseBody);
    })();
  }
  /**
   * @name deviceAuthorization
   * @api public
   */


  deviceAuthorization(params = {}, {
    exchangeBody,
    clientAssertionPayload
  } = {}) {
    var _this17 = this;

    return _asyncToGenerator(function* () {
      assertIssuerConfiguration(_this17.issuer, 'device_authorization_endpoint');
      assertIssuerConfiguration(_this17.issuer, 'token_endpoint');
      const body = authorizationParams.call(_this17, {
        client_id: _this17.client_id,
        redirect_uri: null,
        response_type: null,
        ...params
      });
      const response = yield authenticatedPost.call(_this17, 'device_authorization', {
        form: true,
        body,
        json: true
      }, {
        clientAssertionPayload,
        endpointAuthMethod: 'token'
      });
      const responseBody = processResponse(response);
      return new DeviceFlowHandle({
        client: _this17,
        exchangeBody,
        clientAssertionPayload,
        response: responseBody,
        maxAge: params.max_age
      });
    })();
  }
  /**
   * @name revoke
   * @api public
   */


  revoke(token, hint, {
    revokeBody,
    clientAssertionPayload
  } = {}) {
    var _this18 = this;

    return _asyncToGenerator(function* () {
      assertIssuerConfiguration(_this18.issuer, 'revocation_endpoint');

      if (hint !== undefined && typeof hint !== 'string') {
        throw new TypeError('hint must be a string');
      }

      const body = { ...revokeBody,
        token
      };

      if (hint) {
        body.token_type_hint = hint;
      }

      const response = yield authenticatedPost.call(_this18, 'revocation', {
        body,
        form: true
      }, {
        clientAssertionPayload
      });
      processResponse(response, {
        body: false
      });
    })();
  }
  /**
   * @name introspect
   * @api public
   */


  introspect(token, hint, {
    introspectBody,
    clientAssertionPayload
  } = {}) {
    var _this19 = this;

    return _asyncToGenerator(function* () {
      assertIssuerConfiguration(_this19.issuer, 'introspection_endpoint');

      if (hint !== undefined && typeof hint !== 'string') {
        throw new TypeError('hint must be a string');
      }

      const body = { ...introspectBody,
        token
      };

      if (hint) {
        body.token_type_hint = hint;
      }

      const response = yield authenticatedPost.call(_this19, 'introspection', {
        body,
        form: true,
        json: true
      }, {
        clientAssertionPayload
      });
      const responseBody = processResponse(response);
      return responseBody;
    })();
  }
  /**
   * @name fetchDistributedClaims
   * @api public
   */


  fetchDistributedClaims(claims, tokens = {}) {
    var _this20 = this;

    return _asyncToGenerator(function* () {
      if (!isPlainObject(claims)) {
        throw new TypeError('claims argument must be a plain object');
      }

      if (!isPlainObject(claims._claim_sources)) {
        return claims;
      }

      if (!isPlainObject(claims._claim_names)) {
        return claims;
      }

      const distributedSources = Object.entries(claims._claim_sources).filter(([, value]) => value && value.endpoint);
      yield Promise.all(distributedSources.map( /*#__PURE__*/function () {
        var _ref = _asyncToGenerator(function* ([sourceName, def]) {
          try {
            const requestOpts = {
              headers: {
                Accept: 'application/jwt',
                Authorization: authorizationHeaderValue(def.access_token || tokens[sourceName])
              }
            };
            const response = yield request.call(_this20, { ...requestOpts,
              method: 'GET',
              url: def.endpoint
            });
            const body = processResponse(response, {
              bearer: true
            });
            const decoded = yield claimJWT.call(_this20, 'distributed', body);
            delete claims._claim_sources[sourceName];
            Object.entries(claims._claim_names).forEach(assignClaim(claims, decoded, sourceName, false));
          } catch (err) {
            err.src = sourceName;
            throw err;
          }
        });

        return function (_x3) {
          return _ref.apply(this, arguments);
        };
      }()));
      cleanUpClaims(claims);
      return claims;
    })();
  }
  /**
   * @name unpackAggregatedClaims
   * @api public
   */


  unpackAggregatedClaims(claims) {
    var _this21 = this;

    return _asyncToGenerator(function* () {
      if (!isPlainObject(claims)) {
        throw new TypeError('claims argument must be a plain object');
      }

      if (!isPlainObject(claims._claim_sources)) {
        return claims;
      }

      if (!isPlainObject(claims._claim_names)) {
        return claims;
      }

      const aggregatedSources = Object.entries(claims._claim_sources).filter(([, value]) => value && value.JWT);
      yield Promise.all(aggregatedSources.map( /*#__PURE__*/function () {
        var _ref2 = _asyncToGenerator(function* ([sourceName, def]) {
          try {
            const decoded = yield claimJWT.call(_this21, 'aggregated', def.JWT);
            delete claims._claim_sources[sourceName];
            Object.entries(claims._claim_names).forEach(assignClaim(claims, decoded, sourceName));
          } catch (err) {
            err.src = sourceName;
            throw err;
          }
        });

        return function (_x4) {
          return _ref2.apply(this, arguments);
        };
      }()));
      cleanUpClaims(claims);
      return claims;
    })();
  }
  /**
   * @name register
   * @api public
   */


  static register(metadata, options = {}) {
    var _this22 = this;

    return _asyncToGenerator(function* () {
      const {
        initialAccessToken,
        jwks,
        ...clientOptions
      } = options;
      assertIssuerConfiguration(_this22.issuer, 'registration_endpoint');

      if (jwks !== undefined && !(metadata.jwks || metadata.jwks_uri)) {
        const keystore = getKeystore.call(_this22, jwks);
        metadata.jwks = keystore.toJWKS(false);
      }

      const response = yield request.call(_this22, {
        headers: initialAccessToken ? {
          Authorization: authorizationHeaderValue(initialAccessToken)
        } : undefined,
        json: true,
        body: metadata,
        url: _this22.issuer.registration_endpoint,
        method: 'POST'
      });
      const responseBody = processResponse(response, {
        statusCode: 201,
        bearer: true
      });
      return new _this22(responseBody, jwks, clientOptions);
    })();
  }
  /**
   * @name metadata
   * @api public
   */


  get metadata() {
    const copy = {};
    instance(this).get('metadata').forEach((value, key) => {
      copy[key] = value;
    });
    return copy;
  }
  /**
   * @name fromUri
   * @api public
   */


  static fromUri(registrationClientUri, registrationAccessToken, jwks, clientOptions) {
    var _this23 = this;

    return _asyncToGenerator(function* () {
      const response = yield request.call(_this23, {
        method: 'GET',
        url: registrationClientUri,
        json: true,
        headers: {
          Authorization: authorizationHeaderValue(registrationAccessToken)
        }
      });
      const responseBody = processResponse(response, {
        bearer: true
      });
      return new _this23(responseBody, jwks, clientOptions);
    })();
  }
  /**
   * @name requestObject
   * @api public
   */


  requestObject(requestObject = {}, {
    sign: signingAlgorithm = this.request_object_signing_alg || 'none',
    encrypt: {
      alg: eKeyManagement = this.request_object_encryption_alg,
      enc: eContentEncryption = this.request_object_encryption_enc || 'A128CBC-HS256'
    } = {}
  } = {}) {
    var _this24 = this;

    return _asyncToGenerator(function* () {
      if (!isPlainObject(requestObject)) {
        throw new TypeError('requestObject must be a plain object');
      }

      let signed;
      let key;
      const header = {
        alg: signingAlgorithm,
        typ: 'JWT'
      };
      const payload = JSON.stringify(defaults({}, requestObject, {
        iss: _this24.client_id,
        aud: _this24.issuer.issuer,
        client_id: _this24.client_id,
        jti: random(),
        iat: now(),
        exp: now() + 300
      }));

      if (signingAlgorithm === 'none') {
        signed = [base64url.encode(JSON.stringify(header)), base64url.encode(payload), ''].join('.');
      } else {
        const symmetric = signingAlgorithm.startsWith('HS');

        if (symmetric) {
          key = yield _this24.joseSecret();
        } else {
          const keystore = instance(_this24).get('keystore');

          if (!keystore) {
            throw new TypeError(`no keystore present for client, cannot sign using alg ${signingAlgorithm}`);
          }

          key = keystore.get({
            alg: signingAlgorithm,
            use: 'sig'
          });

          if (!key) {
            throw new TypeError(`no key to sign with found for alg ${signingAlgorithm}`);
          }
        }

        signed = jose.JWS.sign(payload, key, { ...header,
          kid: symmetric ? undefined : key.kid
        });
      }

      if (!eKeyManagement) {
        return signed;
      }

      const fields = {
        alg: eKeyManagement,
        enc: eContentEncryption,
        cty: 'JWT'
      };

      if (fields.alg.match(/^(RSA|ECDH)/)) {
        [key] = yield _this24.issuer.queryKeyStore({
          alg: fields.alg,
          enc: fields.enc,
          use: 'enc'
        }, {
          allowMulti: true
        });
      } else {
        key = yield _this24.joseSecret(fields.alg === 'dir' ? fields.enc : fields.alg);
      }

      return jose.JWE.encrypt(signed, key, { ...fields,
        kid: key.kty === 'oct' ? undefined : key.kid
      });
    })();
  }
  /**
   * @name issuer
   * @api public
   */


  static get issuer() {
    return issuer;
  }
  /**
   * @name issuer
   * @api public
   */


  get issuer() {
    // eslint-disable-line class-methods-use-this
    return issuer;
  }
  /* istanbul ignore next */


  [inspect.custom]() {
    return `${this.constructor.name} ${inspect(this.metadata, {
      depth: Infinity,
      colors: process.stdout.isTTY,
      compact: false,
      sorted: true
    })}`;
  }

}; // TODO: remove in 4.x


BaseClient.prototype.resource = deprecate(
/*#__PURE__*/

/* istanbul ignore next */
function () {
  var _resource = _asyncToGenerator(function* (resourceUrl, accessToken, options) {
    let token = accessToken;
    const opts = {
      verb: 'GET',
      via: 'header',
      ...options
    };

    if (token instanceof TokenSet) {
      if (!token.access_token) {
        throw new TypeError('access_token not present in TokenSet');
      }

      opts.tokenType = opts.tokenType || token.token_type;
      token = token.access_token;
    }

    const verb = String(opts.verb).toUpperCase();
    let requestOpts;

    switch (opts.via) {
      case 'query':
        if (verb !== 'GET') {
          throw new TypeError('resource servers should only parse query strings for GET requests');
        }

        requestOpts = {
          query: {
            access_token: token
          }
        };
        break;

      case 'body':
        if (verb !== 'POST') {
          throw new TypeError('can only send body on POST');
        }

        requestOpts = {
          form: true,
          body: {
            access_token: token
          }
        };
        break;

      default:
        requestOpts = {
          headers: {
            Authorization: authorizationHeaderValue(token, opts.tokenType)
          }
        };
    }

    if (opts.params) {
      if (verb === 'POST') {
        defaultsDeep(requestOpts, {
          body: opts.params
        });
      } else {
        defaultsDeep(requestOpts, {
          query: opts.params
        });
      }
    }

    if (opts.headers) {
      defaultsDeep(requestOpts, {
        headers: opts.headers
      });
    }

    const mTLS = !!this.tls_client_certificate_bound_access_tokens;
    return request.call(this, { ...requestOpts,
      encoding: null,
      method: verb,
      url: resourceUrl
    }, {
      mTLS
    });
  });

  function resource(_x5, _x6, _x7) {
    return _resource.apply(this, arguments);
  }

  return resource;
}(), 'client.resource() is deprecated, use client.requestResource() instead, see docs for API details');
module.exports.BaseClient = BaseClient;